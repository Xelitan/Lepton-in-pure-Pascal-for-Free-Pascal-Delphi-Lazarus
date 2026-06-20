unit LeptonFile;

{$mode delphi}
{$H+}
{$R-}
{$Q-}
{$modeswitch advancedrecords}

// LEPTON - JPEG encoder/decoder
// Based on Microsoft's code in Ruby
// Author: www.xelitan.com/
// License: MIT
//
// Port of `structs/lepton_header.rs`, `structs/lepton_file_writer.rs`,
//  `structs/lepton_file_reader.rs` and the framing part of
//  `structs/multiplexer.rs`, simplified to a single partition / single thread.
//
//  Entry points: EncodeLepton (JPEG -> LEPTON) and DecodeLepton (LEPTON -> JPEG).

interface

uses
  Classes, SysUtils, ZStream,
  LeptonConsts, LeptonErrors, LeptonFeatures,
  JpegHeader, JpegComponentInfo, JpegRead, JpegWrite, JpegScanDecoder,
  JpegRowSpec, TruncateComponents,
  LeptonCore;

procedure EncodeLepton(InStream, OutStream: TStream; const Features: TEnabledFeatures);
procedure DecodeLepton(InStream, OutStream: TStream; const Features: TEnabledFeatures);

// Encodes and then immediately decodes in memory, verifying that the round-trip
//  reproduces the original JPEG byte-for-byte before writing the LEPTON output.
//  Raises lecVerification* on mismatch so we never silently lose data.
procedure EncodeLeptonVerify(InStream, OutStream: TStream; const Features: TEnabledFeatures);

implementation

const
  LEPTON_VERSION_B = 1;

// ---------- little-endian helpers ----------

procedure WriteU8(S: TStream; B: Byte); inline;
begin
  S.WriteBuffer(B, 1);
end;

procedure WriteU16LE(S: TStream; V: Word);
var B: array[0..1] of Byte;
begin
  B[0] := Byte(V); B[1] := Byte(V shr 8);
  S.WriteBuffer(B, 2);
end;

procedure WriteU32LE(S: TStream; V: LongWord);
var B: array[0..3] of Byte;
begin
  B[0] := Byte(V); B[1] := Byte(V shr 8); B[2] := Byte(V shr 16); B[3] := Byte(V shr 24);
  S.WriteBuffer(B, 4);
end;

procedure WriteBytesTo(S: TStream; const A: TBytes);
begin
  if Length(A) > 0 then
    S.WriteBuffer(A[0], Length(A));
end;

function ReadU16LE(const Buf: TBytes; Pos: Integer): Word; inline;
begin
  Result := Word(Buf[Pos]) or (Word(Buf[Pos + 1]) shl 8);
end;

function ReadU32LEBuf(const Buf: TBytes; Pos: Integer): LongWord; inline;
begin
  Result := LongWord(Buf[Pos]) or (LongWord(Buf[Pos + 1]) shl 8) or
    (LongWord(Buf[Pos + 2]) shl 16) or (LongWord(Buf[Pos + 3]) shl 24);
end;

function FloorLog2(V: LongWord): Integer;
begin
  Result := 0;
  while V > 1 do begin V := V shr 1; Inc(Result); end;
end;

// ---------- zlib ----------

function ZlibCompress(const Src: TBytes): TBytes;
var
  Dest: TMemoryStream;
  CS: Tcompressionstream;
begin
  Dest := TMemoryStream.Create;
  try
    CS := Tcompressionstream.Create(cldefault, Dest);
    try
      if Length(Src) > 0 then
        CS.WriteBuffer(Src[0], Length(Src));
    finally
      CS.Free; // flush
    end;
    SetLength(Result, Dest.Size);
    if Dest.Size > 0 then
    begin
      Dest.Position := 0;
      Dest.ReadBuffer(Result[0], Dest.Size);
    end;
  finally
    Dest.Free;
  end;
end;

function ZlibDecompress(const Src: TBytes): TBytes;
var
  SrcStream: TMemoryStream;
  DS: Tdecompressionstream;
  Buf: array[0..16383] of Byte;
  N: LongInt;
  Out_: TMemoryStream;
begin
  SrcStream := TMemoryStream.Create;
  Out_ := TMemoryStream.Create;
  try
    if Length(Src) > 0 then
      SrcStream.WriteBuffer(Src[0], Length(Src));
    SrcStream.Position := 0;
    DS := Tdecompressionstream.Create(SrcStream);
    try
      repeat
        N := DS.Read(Buf, SizeOf(Buf));
        if N > 0 then
          Out_.WriteBuffer(Buf, N);
      until N <= 0;
    finally
      DS.Free;
    end;
    SetLength(Result, Out_.Size);
    if Out_.Size > 0 then
    begin
      Out_.Position := 0;
      Out_.ReadBuffer(Result[0], Out_.Size);
    end;
  finally
    SrcStream.Free;
    Out_.Free;
  end;
end;

// ---------- multiplex framing (single partition, tid=0) ----------

procedure MultiplexFrame(OutStream: TStream; const Data: TBytes);
var
  Pos, Len, Chunk, L: Integer;
begin
  Len := Length(Data);
  Pos := 0;
  if Len = 0 then
  begin
    // emit an empty 3-byte-header... never happens for real data; guard anyway
    Exit;
  end;
  while Pos < Len do
  begin
    Chunk := Len - Pos;
    if Chunk > 65536 then Chunk := 65536;
    L := Chunk - 1;
    if (L = 4095) or (L = 16383) or (L = 65535) then
      WriteU8(OutStream, Byte(((FloorLog2(L) shr 1) - 4) shl 4))
    else
    begin
      WriteU8(OutStream, 0);
      WriteU8(OutStream, Byte(L and $FF));
      WriteU8(OutStream, Byte((L shr 8) and $FF));
    end;
    OutStream.WriteBuffer(Data[Pos], Chunk);
    Inc(Pos, Chunk);
  end;
end;

function MultiplexDeframe(const Buf: TBytes; StartPos, EndPos: Integer): TBytes;
var
  Pos, DataLen, Flags, OutLen: Integer;
  Marker: Byte;
  Out_: TMemoryStream;
begin
  Out_ := TMemoryStream.Create;
  try
    Pos := StartPos;
    while Pos < EndPos do
    begin
      Marker := Buf[Pos]; Inc(Pos);
      if Marker < 16 then
      begin
        if Pos + 2 > EndPos then Break;
        DataLen := (Integer(Buf[Pos + 1]) shl 8) + Integer(Buf[Pos]) + 1;
        Inc(Pos, 2);
      end
      else
      begin
        Flags := (Marker shr 4) and 3;
        DataLen := 1024 shl (2 * Flags);
      end;
      if Pos + DataLen > EndPos then
        DataLen := EndPos - Pos;
      if DataLen > 0 then
        Out_.WriteBuffer(Buf[Pos], DataLen);
      Inc(Pos, DataLen);
    end;
    OutLen := Out_.Size;
    SetLength(Result, OutLen);
    if OutLen > 0 then
    begin
      Out_.Position := 0;
      Out_.ReadBuffer(Result[0], OutLen);
    end;
  finally
    Out_.Free;
  end;
end;

// ---------- inner lepton header (uncompressed) ----------

procedure WriteInnerHeader(S: TStream; const RInfo: TReconstructionInfo;
  LumaYStart: LongWord);
var
  I: Integer;
begin
  // HDR + raw jpeg header
  S.WriteBuffer(LeptonHeaderMarker[0], 3);
  WriteU32LE(S, Length(RInfo.RawJpegHeader));
  WriteBytesTo(S, RInfo.RawJpegHeader);

  // P0D pad bit
  S.WriteBuffer(LeptonHeaderPadMarker[0], 3);
  if RInfo.HasPadBit then
    WriteU8(S, RInfo.PadBit)
  else
    WriteU8(S, 0);

  // HH luma split: thread handoff serialize (single thread)
  S.WriteBuffer(LeptonHeaderLumaSplitMarker[0], 2);
  WriteU8(S, 1); // count
  WriteU16LE(S, Word(LumaYStart));   // luma_y_start
  WriteU32LE(S, 0);                  // segment_size (unused by this decoder)
  WriteU8(S, 0);                     // overhang_byte
  WriteU8(S, 0);                     // num_overhang_bits
  for I := 0 to COLOR_CHANNEL_NUM_BLOCK_TYPES - 1 do
    WriteU16LE(S, 0);                // last_dc[i]
  for I := COLOR_CHANNEL_NUM_BLOCK_TYPES to 3 do
    WriteU16LE(S, 0);

  // CRS restart counts
  if Length(RInfo.RstCnt) > 0 then
  begin
    S.WriteBuffer(LeptonHeaderJpgRestartsMarker[0], 3);
    WriteU32LE(S, Length(RInfo.RstCnt));
    for I := 0 to High(RInfo.RstCnt) do
      WriteU32LE(S, RInfo.RstCnt[I]);
  end;

  // FRS restart errors
  if Length(RInfo.RstErr) > 0 then
  begin
    S.WriteBuffer(LeptonHeaderJpgRestartErrorsMarker[0], 3);
    WriteU32LE(S, Length(RInfo.RstErr));
    WriteBytesTo(S, RInfo.RstErr);
  end;

  // EEE early eof
  if RInfo.EarlyEOFEncountered then
  begin
    S.WriteBuffer(LeptonHeaderEarlyEofMarker[0], 3);
    WriteU32LE(S, RInfo.MaxCmp);
    WriteU32LE(S, RInfo.MaxBPos);
    WriteU32LE(S, RInfo.MaxSAH);
    WriteU32LE(S, RInfo.MaxDPos[0]);
    WriteU32LE(S, RInfo.MaxDPos[1]);
    WriteU32LE(S, RInfo.MaxDPos[2]);
    WriteU32LE(S, RInfo.MaxDPos[3]);
  end;

  // GRB garbage
  if Length(RInfo.GarbageData) > 0 then
  begin
    S.WriteBuffer(LeptonHeaderGarbageMarker[0], 3);
    WriteU32LE(S, Length(RInfo.GarbageData));
    WriteBytesTo(S, RInfo.GarbageData);
  end;
end;

function MarkerMatch(const Buf: TBytes; Pos: Integer; const M: array of Byte; Len: Integer): Boolean;
var I: Integer;
begin
  Result := True;
  for I := 0 to Len - 1 do
    if Buf[Pos + I] <> M[I] then Exit(False);
end;

procedure ParseInnerHeader(const Inner: TBytes; var RInfo: TReconstructionInfo;
  out RawJpegHeader: TBytes; out LumaYStart: LongWord);
var
  Pos, HdrLen, I, Cnt: Integer;
begin
  Pos := 0;
  LumaYStart := 0;
  SetLength(RawJpegHeader, 0);

  // HDR
  if not MarkerMatch(Inner, Pos, LeptonHeaderMarker, 3) then
    LeptonFail(lecBadLeptonFile, 'HDR marker not found');
  Inc(Pos, 3);
  HdrLen := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
  SetLength(RawJpegHeader, HdrLen);
  if HdrLen > 0 then
    Move(Inner[Pos], RawJpegHeader[0], HdrLen);
  Inc(Pos, HdrLen);

  if Length(RInfo.GarbageData) = 0 then
  begin
    SetLength(RInfo.GarbageData, 2);
    RInfo.GarbageData[0] := $FF;
    RInfo.GarbageData[1] := JpegCodeEOI;
  end;

  while Pos + 3 <= Length(Inner) do
  begin
    if MarkerMatch(Inner, Pos, LeptonHeaderPadMarker, 3) then
    begin
      Inc(Pos, 3);
      RInfo.HasPadBit := True;
      RInfo.PadBit := Inner[Pos]; Inc(Pos);
    end
    else if MarkerMatch(Inner, Pos, LeptonHeaderJpgRestartsMarker, 3) then
    begin
      Inc(Pos, 3);
      RInfo.RstCntSet := True;
      Cnt := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      SetLength(RInfo.RstCnt, Cnt);
      for I := 0 to Cnt - 1 do
      begin
        RInfo.RstCnt[I] := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      end;
    end
    else if MarkerMatch(Inner, Pos, LeptonHeaderLumaSplitMarker, 2) then
    begin
      // HH + count byte, then handoffs
      Inc(Pos, 2);
      Cnt := Inner[Pos]; Inc(Pos);
      for I := 0 to Cnt - 1 do
      begin
        if I = 0 then
          LumaYStart := ReadU16LE(Inner, Pos);
        Inc(Pos, 2);            // luma_y_start
        Inc(Pos, 4);            // segment_size
        Inc(Pos, 1);            // overhang_byte
        Inc(Pos, 1);            // num_overhang_bits
        Inc(Pos, 8);            // 4 x i16 last_dc
      end;
    end
    else if MarkerMatch(Inner, Pos, LeptonHeaderJpgRestartErrorsMarker, 3) then
    begin
      Inc(Pos, 3);
      Cnt := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      SetLength(RInfo.RstErr, Cnt);
      if Cnt > 0 then Move(Inner[Pos], RInfo.RstErr[0], Cnt);
      Inc(Pos, Cnt);
    end
    else if MarkerMatch(Inner, Pos, LeptonHeaderGarbageMarker, 3) then
    begin
      Inc(Pos, 3);
      Cnt := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      SetLength(RInfo.GarbageData, Cnt);
      if Cnt > 0 then Move(Inner[Pos], RInfo.GarbageData[0], Cnt);
      Inc(Pos, Cnt);
    end
    else if MarkerMatch(Inner, Pos, LeptonHeaderEarlyEofMarker, 3) then
    begin
      Inc(Pos, 3);
      RInfo.MaxCmp := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxBPos := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxSAH := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxDPos[0] := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxDPos[1] := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxDPos[2] := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.MaxDPos[3] := ReadU32LEBuf(Inner, Pos); Inc(Pos, 4);
      RInfo.EarlyEOFEncountered := True;
    end
    else
      LeptonFail(lecBadLeptonFile, 'unknown data in lepton header');
  end;
end;

// ---------- encode ----------

procedure EncodeLepton(InStream, OutStream: TStream; const Features: TEnabledFeatures);
var
  JpegHeaderObj: TJpegHeader;
  RInfo: TReconstructionInfo;
  ImageData: TBlockBasedImageArray;
  Partitions: TRestartPartitionArray;
  EndScan: Int64;
  Colldata: TTruncateComponents;
  Qts: TQuantizationTablesArray;
  Inner, InnerBytes, Compressed, PartitionData: TBytes;
  InnerStream, PartitionStream: TMemoryStream;
  StartPos: Int64;
  FinalSize: LongWord;
  LumaBcv: LongWord;
  JpegFileSize: LongWord;
begin
  JpegHeaderObj := TJpegHeader.Create;
  try
    RInfo := TReconstructionInfo.Default;
    InStream.Position := 0;
    ReadJpegCoefficientsFromStream(InStream, JpegHeaderObj, RInfo, Features,
      ImageData, Partitions, EndScan);
    JpegFileSize := LongWord(InStream.Size);

    LumaBcv := JpegHeaderObj.CmpInfo[0].BCV;

    // build inner header
    InnerStream := TMemoryStream.Create;
    try
      WriteInnerHeader(InnerStream, RInfo, 0);
      SetLength(Inner, InnerStream.Size);
      if InnerStream.Size > 0 then
      begin
        InnerStream.Position := 0;
        InnerStream.ReadBuffer(Inner[0], InnerStream.Size);
      end;
    finally
      InnerStream.Free;
    end;
    InnerBytes := Inner;
    Compressed := ZlibCompress(InnerBytes);

    StartPos := OutStream.Position;

    // fixed header (28 bytes)
    WriteU8(OutStream, $CF);
    WriteU8(OutStream, $84);
    WriteU8(OutStream, LEPTON_VERSION_B);
    if JpegHeaderObj.JpegType = jtProgressive then
      WriteU8(OutStream, Ord('X'))
    else
      WriteU8(OutStream, Ord('Z'));
    WriteU8(OutStream, 1); // thread count
    WriteU8(OutStream, 0); WriteU8(OutStream, 0); WriteU8(OutStream, 0);
    WriteU8(OutStream, Ord('M'));
    WriteU8(OutStream, Ord('S'));
    WriteU32LE(OutStream, Length(InnerBytes));
    WriteU8(OutStream, Byte($80 or (Ord(Features.Use16BitDcEstimate) and 1)
      or ((Ord(Features.Use16BitAdvPredict) and 1) shl 1)));
    WriteU8(OutStream, 0); // encoder version
    WriteU32LE(OutStream, 0); // git revision prefix (4 bytes)
    WriteU32LE(OutStream, JpegFileSize);
    WriteU32LE(OutStream, Length(Compressed));
    WriteBytesTo(OutStream, Compressed);

    // CMP marker
    OutStream.WriteBuffer(LeptonHeaderCompletionMarker[0], 3);

    // encode coefficients to partition buffer
    Qts := ConstructQuantizationTables(JpegHeaderObj);
    Colldata := TTruncateComponents.Create;
    try
      Colldata.Init(JpegHeaderObj);
      if RInfo.EarlyEOFEncountered then
        Colldata.SetTruncationBounds(JpegHeaderObj, RInfo.MaxDPos);

      PartitionStream := TMemoryStream.Create;
      try
        LeptonEncodeRowRange(Qts, ImageData, PartitionStream, Colldata,
          0, LumaBcv, True, True, Features);
        SetLength(PartitionData, PartitionStream.Size);
        if PartitionStream.Size > 0 then
        begin
          PartitionStream.Position := 0;
          PartitionStream.ReadBuffer(PartitionData[0], PartitionStream.Size);
        end;
      finally
        PartitionStream.Free;
      end;
    finally
      Colldata.Free;
    end;

    // frame into multiplex blocks
    MultiplexFrame(OutStream, PartitionData);

    // final 4-byte size
    FinalSize := LongWord(OutStream.Position - StartPos) + 4;
    WriteU32LE(OutStream, FinalSize);
  finally
    JpegHeaderObj.Free;
  end;
end;

procedure EncodeLeptonVerify(InStream, OutStream: TStream; const Features: TEnabledFeatures);
var
  Lep, VerifyBuf, Orig: TMemoryStream;
  DecFeatures: TEnabledFeatures;
  I: Int64;
  Same: Boolean;
begin
  Lep := TMemoryStream.Create;
  VerifyBuf := TMemoryStream.Create;
  Orig := TMemoryStream.Create;
  try
    InStream.Position := 0;
    Orig.CopyFrom(InStream, InStream.Size);

    Orig.Position := 0;
    EncodeLepton(Orig, Lep, Features);

    // decode the just-encoded lepton stream and compare to the original
    Lep.Position := 0;
    DecFeatures := Features;
    DecodeLepton(Lep, VerifyBuf, DecFeatures);

    Same := Orig.Size = VerifyBuf.Size;
    if not Same then
      LeptonFail(lecVerificationLengthMismatch,
        Format('verify length mismatch: original=%d decoded=%d', [Orig.Size, VerifyBuf.Size]));

    I := 0;
    while I < Orig.Size do
    begin
      if PByte(Orig.Memory)[I] <> PByte(VerifyBuf.Memory)[I] then
        LeptonFail(lecVerificationContentMismatch,
          Format('verify content mismatch at byte %d', [I]));
      Inc(I);
    end;

    Lep.Position := 0;
    OutStream.CopyFrom(Lep, Lep.Size);
  finally
    Lep.Free;
    VerifyBuf.Free;
    Orig.Free;
  end;
end;

// ---------- decode ----------

function AdvanceNextHeaderSegment(JpegHeaderObj: TJpegHeader; const RawJpegHeader: TBytes;
  var ReadIndex: Integer; const Features: TEnabledFeatures): Boolean;
var
  Ms: TMemoryStream;
  Dummy: TReconstructionInfo;
  Remaining: Integer;
begin
  Remaining := Length(RawJpegHeader) - ReadIndex;
  if Remaining <= 0 then Exit(False);
  Ms := TMemoryStream.Create;
  try
    Ms.WriteBuffer(RawJpegHeader[ReadIndex], Remaining);
    Ms.Position := 0;
    Dummy := TReconstructionInfo.Default;
    Result := ParseJpegHeader(Ms, Features, JpegHeaderObj, Dummy);
    Inc(ReadIndex, Integer(Ms.Position));
  finally
    Ms.Free;
  end;
end;

procedure DecodeLepton(InStream, OutStream: TStream; const Features: TEnabledFeatures);
var
  Buf: TBytes;
  L, Pos: Integer;
  CompressedHeaderSize: LongWord;
  JpegType: Byte;
  Flags: Byte;
  Eff: TEnabledFeatures;
  Compressed, Inner, RawJpegHeader, PartitionData: TBytes;
  RInfo: TReconstructionInfo;
  LumaYStart: LongWord;
  JpegHeaderObj: TJpegHeader;
  HdrMs: TMemoryStream;
  DummyR: TReconstructionInfo;
  ReadIndex: Integer;
  Trunc: TTruncateComponents;
  Qts: TQuantizationTablesArray;
  ImageData: TBlockBasedImageArray;
  PartStream: TMemoryStream;
  LumaBcv: LongWord;
  Scan: TBytes;
  Scnc: Integer;
  OldPos: Integer;
  MoreScans: Boolean;
begin
  // read entire input
  InStream.Position := 0;
  L := InStream.Size;
  SetLength(Buf, L);
  if L > 0 then
    InStream.ReadBuffer(Buf[0], L);

  if L < 28 then
    LeptonFail(lecBadLeptonFile, 'file too small');
  if (Buf[0] <> $CF) or (Buf[1] <> $84) then
    LeptonFail(lecBadLeptonFile, 'header doesn''t match');
  if Buf[2] <> LEPTON_VERSION_B then
    LeptonFail(lecBadLeptonFile, 'incompatible version');

  JpegType := Buf[3];
  if (JpegType <> Ord('Z')) and (JpegType <> Ord('X')) then
    LeptonFail(lecBadLeptonFile, 'unknown filetype');

  Eff := Features;
  if (Buf[8] = Ord('M')) and (Buf[9] = Ord('S')) then
  begin
    Flags := Buf[14];
    if (Flags and $80) <> 0 then
    begin
      Eff.Use16BitDcEstimate := (Flags and $01) <> 0;
      Eff.Use16BitAdvPredict := (Flags and $02) <> 0;
    end;
  end;

  CompressedHeaderSize := ReadU32LEBuf(Buf, 24);

  // compressed header
  SetLength(Compressed, CompressedHeaderSize);
  if CompressedHeaderSize > 0 then
    Move(Buf[28], Compressed[0], CompressedHeaderSize);
  Inner := ZlibDecompress(Compressed);

  RInfo := TReconstructionInfo.Default;
  ParseInnerHeader(Inner, RInfo, RawJpegHeader, LumaYStart);
  RInfo.RawJpegHeader := RawJpegHeader;

  Pos := 28 + Integer(CompressedHeaderSize);
  // CMP marker
  if (Pos + 3 > L) or (not MarkerMatch(Buf, Pos, LeptonHeaderCompletionMarker, 3)) then
    LeptonFail(lecBadLeptonFile, 'CMP marker not found');
  Inc(Pos, 3);

  // parse jpeg header from raw to obtain jpeg_header and read index
  JpegHeaderObj := TJpegHeader.Create;
  try
    HdrMs := TMemoryStream.Create;
    try
      if Length(RawJpegHeader) > 0 then
        HdrMs.WriteBuffer(RawJpegHeader[0], Length(RawJpegHeader));
      HdrMs.Position := 0;
      DummyR := TReconstructionInfo.Default;
      ParseJpegHeader(HdrMs, Eff, JpegHeaderObj, DummyR);
      ReadIndex := Integer(HdrMs.Position);
    finally
      HdrMs.Free;
    end;

    Trunc := TTruncateComponents.Create;
    try
      Trunc.Init(JpegHeaderObj);
      if RInfo.EarlyEOFEncountered then
        Trunc.SetTruncationBounds(JpegHeaderObj, RInfo.MaxDPos);

      // de-frame multiplex region [Pos .. L-4)
      PartitionData := MultiplexDeframe(Buf, Pos, L - 4);

      Qts := ConstructQuantizationTables(JpegHeaderObj);
      LumaBcv := JpegHeaderObj.CmpInfo[0].BCV;

      PartStream := TMemoryStream.Create;
      try
        if Length(PartitionData) > 0 then
          PartStream.WriteBuffer(PartitionData[0], Length(PartitionData));
        PartStream.Position := 0;
        LeptonDecodeRowRange(Qts, JpegHeaderObj, Trunc, PartStream,
          0, LumaBcv, True, True, Eff, ImageData);
      finally
        PartStream.Free;
      end;

      // ---- reconstruct jpeg ----
      OutStream.WriteBuffer(SOI[0], 2);
      if ReadIndex > 0 then
        OutStream.WriteBuffer(RawJpegHeader[0], ReadIndex);

      if JpegHeaderObj.IsSingleScan then
      begin
        Scan := JpegWriteEntireScan(ImageData, JpegHeaderObj, RInfo, 0);
        if Length(Scan) > 0 then
          OutStream.WriteBuffer(Scan[0], Length(Scan));
        if Length(RawJpegHeader) - ReadIndex > 0 then
          OutStream.WriteBuffer(RawJpegHeader[ReadIndex], Length(RawJpegHeader) - ReadIndex);
      end
      else
      begin
        Scnc := 0;
        while True do
        begin
          Scan := JpegWriteEntireScan(ImageData, JpegHeaderObj, RInfo, Scnc);
          if Length(Scan) > 0 then
            OutStream.WriteBuffer(Scan[0], Length(Scan));
          OldPos := ReadIndex;
          MoreScans := AdvanceNextHeaderSegment(JpegHeaderObj, RawJpegHeader, ReadIndex, Eff);
          if ReadIndex - OldPos > 0 then
            OutStream.WriteBuffer(RawJpegHeader[OldPos], ReadIndex - OldPos);
          if not MoreScans then Break;
          Inc(Scnc);
        end;
      end;

      // garbage data (includes assumed EOI)
      if Length(RInfo.GarbageData) > 0 then
        OutStream.WriteBuffer(RInfo.GarbageData[0], Length(RInfo.GarbageData));
    finally
      Trunc.Free;
    end;
  finally
    JpegHeaderObj.Free;
  end;
end;

end.
