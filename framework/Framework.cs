// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

using MainHandlers_Compile;
using MainDiskIOHandler_Compile;
using UI_Compile;

using System;
using System.IO;
using System.Collections.Generic;
using System.Security.Cryptography;
using System.Threading.Tasks;

using System.Runtime.InteropServices;

namespace MainDiskIOHandler_Compile {
  // TODO make this actually async lol
  public partial class DiskIOHandler {
    const int BLOCK_SIZE = 8*1024*1024;

    ulong curId = 0;
    Dictionary<ulong, Task> writeReqs;
    Dictionary<ulong, byte[]> readReqs;

    public DiskIOHandler() {
      writeReqs = new Dictionary<ulong, Task>();
      readReqs = new Dictionary<ulong, byte[]>();
    }

    private int readFile(string filename, byte[] res) {
      using (FileStream fs = new FileStream(filename, FileMode.Open)) {
        int actualRead = 0;
        do {
          actualRead += fs.Read(res, actualRead, res.Length-actualRead);
        } while (actualRead != res.Length && fs.Position < fs.Length);
        return actualRead;
      } 
    }

    private void printBytes(byte[] a) {
      for (int i = 0; i < a.Length; i++) {
        Console.Write(a[i] + ",");
      }
      Console.WriteLine("");
    }

    public void writeSync(ulong addr, byte[] sector) {
      //Console.WriteLine("writeSync: " + addr + ", " + sector.Length);

      if (sector.Length > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
        Console.WriteLine(addr);
        Console.WriteLine(sector.Length);
        throw new Exception("writeSync not implemented for these arguments");
      }

      //Native_Compile.BenchmarkingUtil.start();
      using (FileStream fs = new FileStream(getFilename(addr), FileMode.OpenOrCreate, FileAccess.Write))
      {
        //fs.Seek(0, SeekOrigin.Begin);
        fs.Write(sector, 0, sector.Length);
        fs.Flush(true);
      }
      //Native_Compile.BenchmarkingUtil.end();
    }

    public void readSync(ulong addr, ulong len, out byte[] sector) {
      //Console.WriteLine("readSync: " + addr + ", " + len);
      if (addr % BLOCK_SIZE != 0 || len > BLOCK_SIZE) {
        throw new Exception("readSync not implemented for these arguments");
      }

      string filename = getFilename(addr);
      byte[] bytes = new byte[len];
      int actualRead = readFile(filename, bytes);
      if ((ulong)actualRead < len) {
        throw new Exception("readSync did not find enough bytes");
      }

      sector = bytes;
    }

    static async Task WriteTextAsync(string filePath, byte[] data)
    {
      using (FileStream fs = new FileStream(filePath,
        FileMode.OpenOrCreate, FileAccess.Write, FileShare.None,
        bufferSize: 4096, useAsync: true))
      {
        await fs.WriteAsync(data, 0, data.Length);
        await fs.FlushAsync();
      };
    }

    public ulong write(ulong addr, byte[] sector) {
      byte[] copied = new byte[sector.Length];
      Array.Copy(sector, 0, copied, 0, sector.Length);

      ulong id = this.curId;
      this.curId++;

      if (sector.Length > BLOCK_SIZE || addr % BLOCK_SIZE != 0) {
        Console.WriteLine(addr);
        Console.WriteLine(sector.Length);
        throw new Exception("writeSync not implemented for these arguments");
      }
      Task writeTask = WriteTextAsync(getFilename(addr), copied);
      writeReqs[id] = writeTask;

      return id;
    }

    public ulong read(ulong addr, ulong len) {
      byte[] bytes;
      readSync(addr, len, out bytes);

      ulong id = this.curId;
      this.curId++;

      this.readReqs.Add(id, bytes);

      return id;
    }

    ulong readResponseId;
    Dafny.Sequence<byte> readResponseBytes;
    public bool prepareReadResponse() {
      if (this.readReqs.Count > 0) {
        foreach (ulong id in this.readReqs.Keys) {
          readResponseId = id;
          break;
        }
        readResponseBytes = new Dafny.Sequence<byte>(readReqs[readResponseId]);
        readReqs.Remove(readResponseId);
        return true;
      } else {
        return false;
      }
    }
    public void getReadResult(out ulong id, out Dafny.Sequence<byte> sector) {
      id = readResponseId;
      sector = readResponseBytes;
    }

    ulong writeResponseId;
    public bool prepareWriteResponse() {
      bool found = false;
      foreach (var p in this.writeReqs) {
        ulong id = p.Key;
        Task task = p.Value;
        if (task.IsCompleted) {
          this.writeResponseId = id;
          found = true;
          break;
        }
      }
      if (found) {
        writeReqs.Remove(this.writeResponseId);
        return true;
      } else {
        return false;
      }
    }
    public ulong getWriteResult() {
      return this.writeResponseId;
    }
    public void completeWriteTasks() {
      foreach (var p in this.writeReqs) {
        Task task = p.Value;
        task.Wait();
      }
    }
    public void waitForOne() {
      Task[] tasks = new Task[this.writeReqs.Count];
      int i = 0;
      foreach (var p in this.writeReqs) {
        tasks[i] = p.Value;
        i++;
      }
      if (tasks.Length == 0) throw new Exception("waitForOne called with no tasks\n");
      Task.WaitAny(tasks);
    }

    private string getFilename(ulong lba) {
      return ".veribetrfs-storage/" + lba.ToString("X16");
    }
  }
}

class Application {
  // TODO hard-coding these types is annoying... is there another option?
  public BetreeGraphBlockCache_Compile.Constants k;
  public MainHandlers_Compile.HeapState hs;

  public DiskIOHandler io;

  public Application() {
    initialize();
    verbose = true;
  }

  public bool verbose;
  public void log(string s) {
    if (verbose) {
      Console.WriteLine(s);
    }
  }

  public void initialize() {
    __default.InitState(out k, out hs);
    io = new DiskIOHandler();
  }

  public void crash() {
    log("'crashing' and reinitializing");
    log("");
    initialize();
  }

  public void Sync() {
    log("Sync");

    var id = __default.handlePushSync(k, hs, io);
    if (id == 0) {
      throw new Exception("pushSync failed to allocate id");
    }
    log("doing push sync...");

    for (int i = 0; i < 5000; i++) {
      while (this.maybeDoResponse()) { }
      __default.handlePopSync(k, hs, io, id, out bool wait, out bool success);
      if (success) {
        log("doing sync... success!");
        log("");
        return;
      } else if (wait) {
        log("doing wait...");
        io.waitForOne();
      } else {
        log("doing sync...");
      }
    }
    log("giving up");
    throw new Exception("operation didn't finish");
  }

  public void Insert(string key, string val) {
    if (verbose) log("Insert (\"" + key + "\", \"" + val + "\")");
    Insert(
      new Dafny.Sequence<byte>(string_to_bytes(key)),
      new Dafny.Sequence<byte>(string_to_bytes(val))
    );
  }

  public void Insert(byte[] key, byte[] val) {
    Insert(
      new Dafny.Sequence<byte>(key),
      new Dafny.Sequence<byte>(val)
    );
  }

  public void Insert(Dafny.Sequence<byte> key, Dafny.Sequence<byte> val) {
    if (key.Count > (int)KeyType_Compile.__default.MaxLen()) {
      throw new Exception("Insert: key is too long");
    }
    if (val.Count > (int)ValueType_Compile.__default.MaxLen()) {
      throw new Exception("Insert: value is too long");
    }

    for (int i = 0; i < 50; i++) {
      bool success = __default.handleInsert(k, hs, io, key, val);
      // TODO remove this to enable more asyncronocity:
      io.completeWriteTasks();
      this.maybeDoResponse();
      if (success) {
        log("doing insert... success!");
        log("");
        return;
      } else {
        log("doing insert...");
      }
    }
    log("giving up");
    throw new Exception("operation didn't finish");
  }

  public void Query(string key) {
    IList<byte> val_bytes = Query(new Dafny.Sequence<byte>(string_to_bytes(key)));
    if (verbose) {
      string val = bytes_to_string(val_bytes);
      log("Query result is: \"" + val + "\"");
    }
  }

  public void Query(byte[] key) {
    Query(new Dafny.Sequence<byte>(key));
  }

  public void QueryAndExpect(byte[] key, byte[] expected) {
    IList<byte> actual = Query(new Dafny.Sequence<byte>(key));

    if (!byteArraysEqual(actual, expected)) {
      throw new Exception("did not get expected result\n");
    }
  }

  public IList<byte> Query(Dafny.Sequence<byte> key) {
    if (verbose) log("Query \"" + key + "\"");

    if (key.Count > (int)KeyType_Compile.__default.MaxLen()) {
      throw new Exception("Query: key is too long");
    }

    for (int i = 0; i < 50; i++) {
      var result = __default.handleQuery(k, hs, io, key);
      this.maybeDoResponse();
      if (result.is_Some) {
        IList<byte> val_bytes = result.dtor_value.Elements;
        log("doing query... success!");
        log("");
        return val_bytes;
      } else {
        log("doing query...");
      }
    }
    log("giving up");
    throw new Exception("operation didn't finish");
  }

  public SuccResult[] QuerySucc(string key, bool inclusive, ulong target)
  {
    if (verbose) log("Successor query: " + (inclusive ? ">=" : ">") + " " + key + " for " + target + " results");
    SuccResult[] results = QuerySucc(string_to_bytes(key), inclusive, target);
    if (verbose) {
      log("Got " + results.Length + " results");
      for (int i = 0; i < results.Length; i++) {
        log("    " + bytes_to_string(results[i].key.Elements) + " : " + bytes_to_string(results[i].@value.Elements));
      }
    }
    return results;
  }

  public SuccResult[] QuerySucc(byte[] key, bool inclusive, ulong target)
  {
    RangeStart start = inclusive ?
        RangeStart.create_SInclusive(new Dafny.Sequence<byte>(key)) :
        RangeStart.create_SExclusive(new Dafny.Sequence<byte>(key));
    return QuerySucc(start, target);
  }

  public SuccResult[] QuerySucc(RangeStart start, ulong target)
  {
    SuccResult[] all_results = new SuccResult[target];
    ulong found = 0;
    while (found < target) {
      SuccResultList srl = QuerySuccOnce(start, target - found);
      for (int i = 0; i < srl.results.Count && found < target; i++) {
        all_results[found] = srl.results.Elements[i];
        found++;
      }
      if (found == target) {
        break;
      }
      if (srl.end.is_PositiveInf) {
        SuccResult[] trunc_results = new SuccResult[found];
        for (ulong i = 0; i < found; i++) {
          trunc_results[i] = all_results[i];
        }
        return trunc_results;
      }
      if (srl.end.is_EExclusive) {
        start = RangeStart.create_SInclusive(srl.end.dtor_key);
      } else {
        start = RangeStart.create_SExclusive(srl.end.dtor_key);
      }
    }

    return all_results;
  }

  public SuccResultList QuerySuccOnce(RangeStart start, ulong maxToFind)
  {
    if (verbose) log("Succ");

    if (maxToFind == 0) {
      throw new Exception("Succ query should have maxToFind >= 1");
    }

    for (int i = 0; i < 50; i++) {
      var result = __default.handleSucc(k, hs, io, start, maxToFind);
      this.maybeDoResponse();
      if (result.is_Some) {
        log("doing succ ... success!");
        log("");
        return result.dtor_value;
      } else {
        log("doing succ...");
      }
    }
    log("giving up");
    throw new Exception("operation didn't finish");
  }

  public bool maybeDoResponse() {
    if (io.prepareReadResponse()) {
      __default.handleReadResponse(k, hs, io);
      log("doing read response...");
      return true;
    }
    else if (io.prepareWriteResponse()) {
      __default.handleWriteResponse(k, hs, io);
      log("doing write response...");
      return true;
    }
    else {
      return false;
    }
  }

  public static byte[] string_to_bytes(string s) {
    return System.Text.Encoding.UTF8.GetBytes(s);
  }

  public static string bytes_to_string(IList<byte> bytes) {
    byte[] ar = new byte[bytes.Count];
    bytes.CopyTo(ar, 0);
    return System.Text.Encoding.UTF8.GetString(ar);
  }

  bool byteArraysEqual(IList<byte> a, IList<byte> b) {
    if (a.Count != b.Count) return false;
    for (int i = 0; i < a.Count; i++) {
      if (a[i] != b[i]) {
        return false;
      }
    }
    return true;
  }

}

public class FSUtil {
  public static void ClearIfExists() {
    if (System.IO.Directory.Exists(".veribetrfs-storage")) {
      System.IO.Directory.Delete(".veribetrfs-storage", true /* recursive */);
    } 
  }

  public static void Mkfs() {
    Dafny.Map<ulong, Dafny.Sequence<byte>> m = __default.Mkfs();

    if (m.Count == 0) {
      throw new Exception("InitDiskBytes failed.");
    }

    if (System.IO.Directory.Exists(".veribetrfs-storage")) {
      throw new Exception("error: .veribetrfs-storage/ already exists");
    }
    System.IO.Directory.CreateDirectory(".veribetrfs-storage");

    DiskIOHandler io = new DiskIOHandler();

    foreach (ulong lba in m.Keys.Elements) {
      IList<byte> ilist = m.Select(lba).Elements;
      byte[] bytes = new byte[ilist.Count];
      ilist.CopyTo(bytes, 0);
      io.writeSync(lba, bytes);
    }
  }
}

class Framework {
  public static void Run() {
    Application app = new Application();
    app.Insert("abc", "def");
    app.Insert("xyq", "rawr");
    app.Query("abc");
    app.Query("xyq");
    app.Query("blahblah");
    app.crash();
    app.Query("abc");
    app.Query("xyq");

    app.Insert("abc", "def");
    app.Insert("xyq", "rawr");
    app.Insert("blahblah", "moomoo");
    app.Sync();
    app.crash();
    //app.Query("abc");
    //app.Query("xyq");


    app.QuerySucc("abc", true, 0);
    app.QuerySucc("abc", true, 1);
    app.QuerySucc("abc", true, 2);
    app.QuerySucc("abc", true, 3);
    app.QuerySucc("abc", true, 4);
    app.QuerySucc("abc", false, 4);
    app.QuerySucc("blah", true, 2);
    app.QuerySucc("zzz", true, 2);

    //for (int i = 0; i < 520; i++) {
    //  app.Insert("num" + i.ToString(), "llama");
    //}

    app.Sync();
  }

  public static void Main(string[] args) {
    bool mkfs = false;
    bool allBenchmarks = false;
    String benchmark = null;
    foreach (string arg in args) {
      if (arg.Equals("--mkfs")) {
        mkfs = true;
      }
      if (arg.Equals("--all-benchmarks")) {
        allBenchmarks = true;
      } else if (arg.StartsWith("--benchmark=")) {
        benchmark = arg.Substring(12);
      }
    }

    if (allBenchmarks) {
      Benchmarks b = new Benchmarks();
      b.RunAllBenchmarks();
    } else if (benchmark != null) {
      Benchmarks b = new Benchmarks();
      b.RunBenchmark(benchmark);
    } else if (mkfs) {
      FSUtil.Mkfs();
    } else {
      Run();
    }
  }
}

namespace Maps_Compile {
  public partial class __default
  {
    public static Dafny.Map<K,V> ComputeMapRemove1<K,V>(Dafny.Map<K,V> m, K k)
    {
      return ((System.Func<Dafny.Map<K,V>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<K,V>>();
        foreach (var _1_j in (m).Keys.Elements) {
          if (((m).Contains(_1_j)) && (!(_1_j).Equals(k))) {
            _coll0.Add(new Dafny.Pair<K,V>(_1_j,(m).Select(_1_j)));
          }
        }
        return Dafny.Map<K,V>.FromCollection(_coll0);
      }))();
    }
  }
}

namespace NativeArithmetic_Compile {
  public partial class __default
  {
    public static ulong u64add(ulong a, ulong b)
    {
      return a + b;
    }
  }
}

namespace NativePackedInts_Compile {
  public partial class __default
  {
    public static uint Unpack__LittleEndian__Uint32(Dafny.Sequence<byte> packed, ulong idx)
    {
      return (uint)packed.Elements[(int)idx]
           + (uint)packed.Elements[(int)idx+1] * 0x100
           + (uint)packed.Elements[(int)idx+2] * 0x10000
           + (uint)packed.Elements[(int)idx+3] * 0x1000000;
    }

    public static ulong Unpack__LittleEndian__Uint64(Dafny.Sequence<byte> packed, ulong idx)
    {
      return (ulong)packed.Elements[(int)idx]
           + (ulong)packed.Elements[(int)idx+1] * 0x100
           + (ulong)packed.Elements[(int)idx+2] * 0x10000
           + (ulong)packed.Elements[(int)idx+3] * 0x1000000
           + (ulong)packed.Elements[(int)idx+4] * 0x100000000
           + (ulong)packed.Elements[(int)idx+5] * 0x10000000000
           + (ulong)packed.Elements[(int)idx+6] * 0x1000000000000
           + (ulong)packed.Elements[(int)idx+7] * 0x100000000000000;
    }

    public static void Pack__LittleEndian__Uint32__into__Array(uint i, byte[] ar, ulong idx)
    {
      ar[idx] = (byte)(i & 0xff);
      ar[idx+1] = (byte)((i >> 8) & 0xff);
      ar[idx+2] = (byte)((i >> 16) & 0xff);
      ar[idx+3] = (byte)((i >> 24) & 0xff);
    }

    public static void Pack__LittleEndian__Uint64__into__Array(ulong i, byte[] ar, ulong idx)
    {
      ar[idx] = (byte)(i & 0xff);
      ar[idx+1] = (byte)((i >> 8) & 0xff);
      ar[idx+2] = (byte)((i >> 16) & 0xff);
      ar[idx+3] = (byte)((i >> 24) & 0xff);
      ar[idx+4] = (byte)((i >> 32) & 0xff);
      ar[idx+5] = (byte)((i >> 40) & 0xff);
      ar[idx+6] = (byte)((i >> 48) & 0xff);
      ar[idx+7] = (byte)((i >> 56) & 0xff);
    }

    public static Dafny.Sequence<uint> Unpack__LittleEndian__Uint32__Seq(Dafny.Sequence<byte> packed, ulong idx, ulong len)
    {
      uint[] ar = new uint[len];
      for (ulong i = 0; i < len; i++) {
        ar[i] = Unpack__LittleEndian__Uint32(packed, idx + 4*i);
      }
      return new Dafny.Sequence<uint>(ar);
    }

    public static Dafny.Sequence<ulong> Unpack__LittleEndian__Uint64__Seq(Dafny.Sequence<byte> packed, ulong idx, ulong len)
    {
      ulong[] ar = new ulong[len];
      for (ulong i = 0; i < len; i++) {
        ar[i] = Unpack__LittleEndian__Uint64(packed, idx + 8*i);
      }
      return new Dafny.Sequence<ulong>(ar);
    }
    
    public static void Pack__LittleEndian__Uint32__Seq__into__Array(Dafny.Sequence<uint> unpacked, byte[] ar, ulong idx)
    {
      for (int i = 0; i < unpacked.Count; i++) {
        Pack__LittleEndian__Uint32__into__Array(unpacked.Elements[i], ar, idx + 4*(ulong)i);
      }
    }
 
    public static void Pack__LittleEndian__Uint64__Seq__into__Array(Dafny.Sequence<ulong> unpacked, byte[] ar, ulong idx)
    {
      for (int i = 0; i < unpacked.Count; i++) {
        Pack__LittleEndian__Uint64__into__Array(unpacked.Elements[i], ar, idx + 8*(ulong)i);
      }
    }

  }
}

namespace NativeArrays_Compile {
  public partial class __default
  {
    public static T[] @newArrayFill<T>(ulong n, T t)
    {
      T[] res = new T[n];
      for (ulong i = 0; i < n; i++) {
        res[i] = t;
      }
      return res;
    }

    public static void @CopyArrayIntoArray<A>(A[] src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
        System.Array.Copy(src, (long)srcIndex, dst, (long)dstIndex, (long)len);
    }

    public static T[] @newArrayClone<T>(T[] ar)
    {
      T[] res = new T[ar.Length];
      System.Array.Copy(ar, 0, res, 0, ar.Length);
      return res;
    }

    public static void @CopySeqIntoArray<A>(Dafny.Sequence<A> src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
        ArraySegment<A> seg = (ArraySegment<A>) src.Elements;
        System.Array.Copy(seg.Array, seg.Offset + (long)srcIndex, dst, (long)dstIndex, (long)len);
    }

    public static void @CopyArrayIntoDifferentArray<A>(A[] src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
        System.Array.Copy(src, (long)srcIndex, dst, (long)dstIndex, (long)len);
    }

    //[DllImport("c", CallingConvention = CallingConvention.Cdecl)]
    [DllImport("msvcrt.dll", CallingConvention=CallingConvention.Cdecl)]
    private static extern unsafe int memcmp(byte* b1, byte* b2, int count);

    public static int @ByteSeqCmpByteSeq(
      Dafny.Sequence<byte> s1,
      Dafny.Sequence<byte> s2)
    {
      var seg1 = (ArraySegment<byte>) s1.Elements;
      var seg2 = (ArraySegment<byte>) s2.Elements;

      int result;
      unsafe {
        fixed (byte* b1 = seg1.Array) {
          fixed (byte* b2 = seg2.Array) {
            result = memcmp(b1 + seg1.Offset, b2 + seg2.Offset, Math.Min(seg1.Count, seg2.Count));
          }
        }
      }

      if (result < 0) {
        return -1;
      } else if (result > 0) {
        return 1;
      } else if (seg1.Count < seg2.Count) {
        return -1;
      } else if (seg1.Count > seg2.Count) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}

namespace Crypto_Compile {
  public partial class __default {
    public static Dafny.Sequence<byte> Sha256(Dafny.Sequence<byte> seq)
    {
      //Native_Compile.BenchmarkingUtil.start();
      using (SHA256 mySHA256 = SHA256.Create()) {
        IList<byte> ilist = seq.Elements;
        byte[] bytes = new byte[ilist.Count];
        ilist.CopyTo(bytes, 0);

        byte[] hash = mySHA256.ComputeHash(bytes);
        //Native_Compile.BenchmarkingUtil.end();
        return new Dafny.Sequence<byte>(hash);
      }
    }

    private static readonly Force.Crc32.Crc32Algo _crc32algo = new Force.Crc32.Crc32Algo();

    public static Dafny.Sequence<byte> padded_crc32(byte[] ar, int offset, int length)
    {
      uint currentCrc = 0;

      if (length > 0) {
          currentCrc = _crc32algo.Append(currentCrc, ar, offset, length);
      }

      byte[] hash = System.BitConverter.GetBytes(currentCrc);
      // Pad to 32 bytes
      byte[] padded = new byte[32];
      padded[0] = hash[0];
      padded[1] = hash[1];
      padded[2] = hash[2];
      padded[3] = hash[3];
      for (int i = 4; i < 32; i++) padded[i] = 0;

      return new Dafny.Sequence<byte>(padded);
    }

    public static Dafny.Sequence<byte> Crc32C(Dafny.Sequence<byte> seq)
    {
      ArraySegment<byte> seg = (ArraySegment<byte>) seq.Elements;
      return padded_crc32(seg.Array, seg.Offset, seg.Count);
    }

    public static Dafny.Sequence<byte> Crc32CArray(byte[] ar, ulong start, ulong len)
    {
      return padded_crc32(ar, (int)start, (int)len);
    }
  }
}
