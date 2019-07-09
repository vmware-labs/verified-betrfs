using Impl_Compile;

using System;
using System.IO;

namespace Impl_Compile {
  public partial class DiskIOHandler {
    const int BLOCK_SIZE = 8*1024*1024;

    public void write(ulong lba, byte[] sector) {
      if (sector.Length != BLOCK_SIZE) {
        // We should never get here due to the contract.
        throw new Exception("Block must be exactly BLOCK_SIZE bytes");
      }

      File.WriteAllBytes(getFilename(lba), sector);
    }

    public void read(ulong lba, out byte[] sector) {
      string filename = getFilename(lba);
      byte[] bytes = File.ReadAllBytes(filename);
      if (bytes.Length != BLOCK_SIZE) {
        throw new Exception("Invalid block at " + filename);
      }
      sector = bytes;
    }

    private string getFilename(ulong lba) {
      return "filesystem/" + lba.ToString("X16");
    }
  }
}

class Application {
  // TODO hard-coding these types is annoying... is there another option?
  public BetreeGraphBlockCache_Compile.Constants k;
  public Impl_Compile.ImplHeapState hs;

  public DiskIOHandler io;

  public Application() {
    initialize();
  }

  public void initialize() {
    __default.InitState(out k, out hs);
    io = new DiskIOHandler();
  }

  public void crash() {
    Console.WriteLine("'crashing' and reinitializing");
    Console.WriteLine("");
    initialize();
  }

  public void Sync() {
    Console.WriteLine("Sync");

    for (int i = 0; i < 50; i++) {
      __default.handleSync(k, hs, io, out bool success);
      if (success) {
        Console.WriteLine("doing sync... success!");
        Console.WriteLine("");
        return;
      } else {
        Console.WriteLine("doing sync...");
      }
    }
    Console.WriteLine("giving up");
    throw new Exception("operation didn't finish");
  }

  public void Insert(string key, string val) {
    Console.WriteLine("Insert (\"" + key + "\", \"" + val + "\")");

    Dafny.Sequence<byte> key_bytes = new Dafny.Sequence<byte>(string_to_bytes(key));
    Dafny.Sequence<byte> val_bytes = new Dafny.Sequence<byte>(string_to_bytes(val));

    for (int i = 0; i < 50; i++) {
      __default.handleInsert(k, hs, io, key_bytes, val_bytes, out bool success);
      if (success) {
        Console.WriteLine("doing insert... success!");
        Console.WriteLine("");
        return;
      } else {
        Console.WriteLine("doing insert...");
      }
    }
    Console.WriteLine("giving up");
    throw new Exception("operation didn't finish");
  }

  public void Query(string key) {
    Console.WriteLine("Query \"" + key + "\"");

    Dafny.Sequence<byte> key_bytes = new Dafny.Sequence<byte>(string_to_bytes(key));

    for (int i = 0; i < 50; i++) {
      __default.handleQuery(k, hs, io, key_bytes, out var result);
      if (result.is_Some) {
        byte[] val_bytes = result.dtor_value.Elements;
        string val = bytes_to_string(val_bytes);
        Console.WriteLine("doing query... success! Query result is: \"" + val + "\"");
        Console.WriteLine("");
        return;
      } else {
        Console.WriteLine("doing query...");
      }
    }
    Console.WriteLine("giving up");
    throw new Exception("operation didn't finish");
  }

  public static byte[] string_to_bytes(string s) {
    return System.Text.Encoding.UTF8.GetBytes(s);
  }

  public static string bytes_to_string(byte[] bytes) {
    return System.Text.Encoding.UTF8.GetString(bytes);
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
  }

  public static void Mkfs() {
    Dafny.Map<ulong, byte[]> m;
    MkfsImpl_Compile.__default.InitDiskBytes(out m);

    if (m.Count == 0) {
      throw new Exception("InitDiskBytes failed.");
    }

    if (System.IO.Directory.Exists("filesystem")) {
      throw new Exception("error: filesystem/ already exists");
    }
    System.IO.Directory.CreateDirectory("filesystem");

    DiskIOHandler io = new DiskIOHandler();

    foreach (ulong lba in m.Keys.Elements) {
      byte[] bytes = m.Select(lba);
      io.write(lba, bytes);
    }
  }

  public static void Main(string[] args) {
    bool mkfs = false;
    foreach (string arg in args) {
      if (arg.Equals("--mkfs")) {
        mkfs = true;
      }
    }

    if (mkfs) {
      Mkfs();
    } else {
      Run();
    }
  }
}

namespace Native_Compile {
  public partial class @Arrays
  {
      public static void @CopySeqIntoArray<A>(Dafny.Sequence<A> src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
          System.Array.Copy(src.Elements, (long)srcIndex, dst, (long)dstIndex, (long)len);
      }
  }
}
