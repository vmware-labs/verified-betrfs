using DiskInterface_Compile; // TODO what to do about mangled namespaces?
using Impl_Compile;

using System;
using System.IO;

class DiskIOHandlerImpl : DiskIOHandler {
  public void write(ulong lba, byte[] sector) {
    File.WriteAllBytes(getFilename(lba), sector);
  }

  public void read(ulong lba, out byte[] sector) {
    string filename = getFilename(lba);
    byte[] bytes = File.ReadAllBytes(filename);
    if (bytes.Length != 1024*1024) {
      throw new Exception("Invalid block at " + filename);
    }
    sector = bytes;
  }

  private string getFilename(ulong lba) {
    return "filesystem/" + lba.ToString("X16");
  }
}

class Framework {
  public static void Run() {
    World w = new World();
    w.diskIOHandler = new DiskIOHandlerImpl();
    w.s = Impl_Compile.__default.InitVariables();

    Impl_Compile.__default.handle(Impl_Compile.__default.InitConstants(), w);
  }

  public static void Mkfs() {
    Dafny.Map<ulong, byte[]> m;
    Mkfs_Compile.__default.InitDiskBytes(out m);

    if (m.Count == 0) {
      throw new Exception("InitDiskBytes failed.");
    }

    if (System.IO.Directory.Exists("filesystem")) {
      throw new Exception("error: filesystem/ already exists");
    }
    System.IO.Directory.CreateDirectory("filesystem");

    DiskIOHandler io = new DiskIOHandlerImpl();

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
