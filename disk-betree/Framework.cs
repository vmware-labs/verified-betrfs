using _23_DiskInterface_Compile; // TODO what to do about mangled namespaces?
using _98_Impl_Compile;

using System;
using System.IO;

class DiskIOHandlerImpl : DiskIOHandler {
  public void write(uint lba, Dafny.Sequence<byte> sector) {
    File.WriteAllBytes(getFilename(lba), sector.Elements);
  }

  public void read(uint lba, out Dafny.Sequence<byte> sector) {
    string filename = getFilename(lba);
    byte[] bytes = File.ReadAllBytes(filename);
    if (bytes.Length != 1024*1024) {
      throw new Exception("Invalid block at " + filename);
    }
    sector = new Dafny.Sequence<byte>(bytes);
  }

  private string getFilename(uint lba) {
    return "filesystem/" + lba.ToString("X8");
  }
}

class Framework {
  public static void Main(string[] args) {
    World w = new World();
    w.diskIOHandler = new DiskIOHandlerImpl();
    w.s = _98_Impl_Compile.__default.InitVariables();

    _98_Impl_Compile.__default.handle(_98_Impl_Compile.__default.InitConstants(), w);
  }
}
