using Impl_Compile;

using System;
using System.IO;

namespace Impl_Compile {
  public partial class DiskIOHandler {
    const int BLOCK_SIZE = 1024*1024;

    public void write(ulong lba, byte[] sector) {
      if (sector.Length < BLOCK_SIZE) {
        Array.Resize(ref sector, BLOCK_SIZE);
      }
      else if (sector.Length > BLOCK_SIZE) {
        // We should never get here due to the contract.
        throw new Exception("Block must be at most BLOCK_SIZE");
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

class Framework {
  public static void Insert(Dafny.Sequence<byte> key, Dafny.Sequence<byte> val) {
    __default.InitState(out var k, out var hs);
    DiskIOHandler io = new DiskIOHandler();

    for (int i = 0; i < 50; i++) {
      __default.handleInsert(k, hs, io, key, val, out bool success);
      if (success) {
        Console.WriteLine("doing insert... success!");
        return;
      } else {
        Console.WriteLine("doing insert...");
      }
    }
    Console.WriteLine("giving up");
  }

  public static void Run() {
    byte[] k = {1, 5, 10};
    byte[] v = {100, 11, 11, 14, 17};
    Insert(new Dafny.Sequence<byte>(k), new Dafny.Sequence<byte>(v));
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
