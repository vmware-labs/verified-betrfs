using MainImpl_Compile;
using MainDiskIOHandler_Compile;

using System;
using System.IO;
using System.Collections.Generic;
using System.Security.Cryptography;

namespace MainDiskIOHandler_Compile {
  // TODO make this actually async lol
  public partial class DiskIOHandler {
    const int BLOCK_SIZE = 8*1024*1024;

    ulong curId = 0;
    HashSet<ulong> writeReqs;
    Dictionary<ulong, byte[]> readReqs;

    public DiskIOHandler() {
      writeReqs = new HashSet<ulong>();
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

      byte[] fileData = new byte[BLOCK_SIZE];
      string filename = getFilename(addr);
      if (File.Exists(filename)) {
        readFile(filename, fileData);
      }

      for (int i = 0; i < sector.Length; i++) {
        fileData[i] = sector[i];
      }

      File.WriteAllBytes(getFilename(addr), sector);
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

    public ulong write(ulong addr, byte[] sector) {
      writeSync(addr, sector);

      ulong id = this.curId;
      this.curId++;

      this.writeReqs.Add(id);

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
      if (this.writeReqs.Count > 0) {
        foreach (ulong id in this.writeReqs) {
          writeResponseId = id;
          break;
        }
        writeReqs.Remove(writeResponseId);
        return true;
      } else {
        return false;
      }
    }
    public ulong getWriteResult() {
      return writeResponseId;
    }

    private string getFilename(ulong lba) {
      return ".veribetrfs-storage/" + lba.ToString("X16");
    }
  }
}

class Application {
  // TODO hard-coding these types is annoying... is there another option?
  public BetreeGraphBlockCache_Compile.Constants k;
  public MainImpl_Compile.HeapState hs;

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
    log("doing push sync...");

    for (int i = 0; i < 5000; i++) {
      bool success = __default.handlePopSync(k, hs, io, id);
      this.maybeDoResponse();
      if (success) {
        log("doing sync... success!");
        log("");
        return;
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
    for (int i = 0; i < 50; i++) {
      bool success = __default.handleInsert(k, hs, io, key, val);
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

  public void maybeDoResponse() {
    if (io.prepareReadResponse()) {
      __default.handleReadResponse(k, hs, io);
      log("doing read response...");
    }
    else if (io.prepareWriteResponse()) {
      __default.handleWriteResponse(k, hs, io);
      log("doing write response...");
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
    Dafny.Map<ulong, byte[]> m = MkfsImpl_Compile.__default.InitDiskBytes();

    if (m.Count == 0) {
      throw new Exception("InitDiskBytes failed.");
    }

    if (System.IO.Directory.Exists(".veribetrfs-storage")) {
      throw new Exception("error: .veribetrfs-storage/ already exists");
    }
    System.IO.Directory.CreateDirectory(".veribetrfs-storage");

    DiskIOHandler io = new DiskIOHandler();

    foreach (ulong lba in m.Keys.Elements) {
      byte[] bytes = m.Select(lba);
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
    app.Sync();
    app.crash();
    app.Query("abc");
    app.Query("xyq");

    for (int i = 0; i < 520; i++) {
      app.Insert("num" + i.ToString(), "llama");
    }

    app.Sync();
  }

  public static void Main(string[] args) {
    bool mkfs = false;
    bool benchmark = false;
    foreach (string arg in args) {
      if (arg.Equals("--mkfs")) {
        mkfs = true;
      }
      if (arg.Equals("--benchmark")) {
        benchmark = true;
      }
    }

    if (benchmark) {
      Benchmarks b = new Benchmarks();
      b.RunAllBenchmarks();
    } else if (mkfs) {
      FSUtil.Mkfs();
    } else {
      Run();
    }
  }
}

namespace Native_Compile {
  public partial class @Arrays
  {
      public static void @CopySeqIntoArray<A>(Dafny.Sequence<A> src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
          // Someone who knows C# better than me can maybe do this faster
          var els = src.Elements;
          for (int i = 0; i < (int)len; i++) {
            dst[(int)dstIndex + i] = els[(int)srcIndex + i];
          }
          //System.Array.Copy(src.Elements, (long)srcIndex, dst, (long)dstIndex, (long)len);
      }

      /*public static void @ByteSeqCmpByteSeq(
        Dafny.Sequence<byte> s1, int i1, int l1,
        Dafny.Sequence<byte> s2, int i2, int l2,
        out int res)
      {
        var span1 = new Span<byte>(s1.Elements, i1, l1);
        var span2 = new Span<byte>(s2.Elements, i2, l2);
        res = span1.SequenceCompareTo(span2);
      }*/
  }
}

namespace Crypto_Compile {
  public partial class __default {
    public static Dafny.Sequence<byte> Sha256(Dafny.Sequence<byte> seq)
    {
      Native_Compile.BenchmarkingUtil.start();
      using (SHA256 mySHA256 = SHA256.Create()) {
        IList<byte> ilist = seq.Elements;
        byte[] bytes = new byte[ilist.Count];
        ilist.CopyTo(bytes, 0);

        byte[] hash = mySHA256.ComputeHash(bytes);
        Native_Compile.BenchmarkingUtil.end();
        return new Dafny.Sequence<byte>(hash);
      }
    }

    public static Dafny.Sequence<byte> Crc32(Dafny.Sequence<byte> seq)
    {
      using (var crc32 = DamienG.Security.Cryptography.Crc32.Create()) {
        IList<byte> ilist = seq.Elements;
        byte[] bytes = new byte[ilist.Count];

        ilist.CopyTo(bytes, 0);

        //Native_Compile.BenchmarkingUtil.start();
        byte[] hash = crc32.ComputeHash(bytes);
        //Native_Compile.BenchmarkingUtil.end();

				// Pad to 32 bytes
				byte[] padded = new byte[32];
				padded[0] = hash[0];
				padded[1] = hash[1];
				padded[2] = hash[2];
				padded[3] = hash[3];
				for (int i = 4; i < 32; i++) padded[i] = 0;

        return new Dafny.Sequence<byte>(padded);
      }
    }

  }
}
