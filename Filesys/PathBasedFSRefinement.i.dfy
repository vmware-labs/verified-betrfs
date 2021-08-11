// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FileSystem.s.dfy"
include "PathBasedFSInv.i.dfy"

module PathBasedFSRefinement {
  import F = FileSystem
  import P = PathBasedFS
  import PInv = PathBasedFSInv
  import opened Options
  import opened FSTypes
  import opened PathSpec

  /// Interpretation Functions

  function IPathMap(fs: P.FileSys) : (F.PathMap)
  requires PInv.Inv(fs)
  {
    imap path :: if P.PathExists(fs, path) then P.GetMeta(fs, path).id else Nonexistent
  }

  function IMetaMap(fs: P.FileSys) : (F.MetaView)
  requires PInv.Inv(fs)
  {
    var path_map := IPathMap(fs);

    imap id : ID :: 
      if id in path_map.Values 
      then var p :| p in path_map && path_map[p] == id; P.GetMeta(fs, p)
      else EmptyMeta
  }

  function IDataMap(fs: P.FileSys) : (F.DataView)
  requires PInv.Inv(fs)
  {
    var path_map := IPathMap(fs);

    imap id : ID :: 
      if id in path_map.Values
      then var p :| p in path_map && path_map[p] == id; P.GetData(fs, p)
      else EmptyData()
  }

  function IStep(step: P.Step) : (i_step: F.Step)
  {
    match step {
      case GetAttrStep(path, attr) => F.GetAttrStep(path, attr)
      case ReadLinkStep(path, link_path) => F.ReadLinkStep(path, link_path)
      case CreateStep(path, m) => F.CreateStep(path, m)
      case DeleteStep(path, ctime) => F.DeleteStep(path, ctime)
      case RenameStep(source, dest, ctime) => F.RenameStep(source, dest, ctime)
      case LinkStep(source, dest, ctime, hiddenName) => F.LinkStep(source, dest, ctime)
      case ChangeAttrStep(path, perm, uid, gid, ctime) => F.ChangeAttrStep(path, perm, uid, gid, ctime)
      case TruncateStep(path, size, time) => F.TruncateStep(path, size, time)
      case ReadStep(path, offset, size, data) => F.ReadStep(path, offset, size, data)
      case WriteStep(path, offset, size, data, time) => F.WriteStep(path, offset, size, data, time)
      case UpdateTimeStep(path, atime, mtime, ctime) => F.UpdateTimeStep(path, atime, mtime, ctime)
      case ReadDirStep(dir, start, results, done) => F.ReadDirStep(dir, start, results, done)
      case _ => F.StutterStep
    }
  }

  function I(fs: P.FileSys) : (F.FileSys)
  requires PInv.Inv(fs)
  {
    F.FileSys(IPathMap(fs), IMetaMap(fs), IDataMap(fs))
  }

  /// Refinement Proofs

  lemma PathExistsEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  requires P.PathExists(fs, path)
  ensures F.PathExists(I(fs), path)
  {
  }

  lemma GetMetaEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  ensures P.GetMeta(fs, path) == I(fs).meta_map[I(fs).path_map[path]]
  {
  }

  lemma NoAliasEquiv(fs: P.FileSys, path: Path)
  requires PInv.Inv(fs)
  requires P.PathExists(fs, path)
  ensures P.NoAlias(fs, path) == F.NoAlias(I(fs), path)
  {
  }

  lemma RefinesInit(fs: P.FileSys)
  requires P.Init(fs)
  requires PInv.Inv(fs)
  ensures F.Init(I(fs))
  {
    assert I(fs).path_map[RootDir] == RootID; // observe
  }

  lemma RefinesNext(fs: P.FileSys, fs': P.FileSys)
  requires PInv.Inv(fs)
  requires P.Next(fs, fs')
  ensures PInv.Inv(fs')
  ensures F.Next(I(fs), I(fs'))
  {
    var step :| P.NextStep(fs, fs', step);
    NextStepPreservesInv(fs, fs', step);
  }

  lemma NextStepPreservesInv(fs: P.FileSys, fs': P.FileSys, step: P.Step)
  requires PInv.Inv(fs)
  requires P.NextStep(fs, fs', step)
  ensures PInv.Inv(fs')
  ensures F.NextStep(I(fs), I(fs'), IStep(step))
  {
    var i_step := IStep(step);

    match step {
      case GetAttrStep(path, ctime) => RefinesGetAttr(fs, fs', path, ctime);
      case ReadLinkStep(path, link_path) => RefinesReadLink(fs, fs', path, link_path);
      case CreateStep(path, m) => RefinesCreate(fs, fs', path, m);

      // ===== TBD =====
      case DeleteStep(path, ctime) => RefinesDelete(fs, fs', path, ctime);
      case RenameStep(source, dest, ctime) => {
        assert i_step == F.RenameStep(source, dest, ctime); // observe
        RefinesRename(fs, fs', source, dest, ctime);
      } 
      case LinkStep(source, dest, ctime, hiddenName) => {
        assert i_step == F.LinkStep(source, dest, ctime); // observe
        RefinesLink(fs, fs', source, dest, ctime, hiddenName);
      }
      case _ => {
        assume false;
      }
    }
  }

  lemma RefinesGetAttr(fs: P.FileSys, fs': P.FileSys, path: Path, attr: MetaData)
  requires PInv.Inv(fs)
  requires P.GetAttr(fs, fs', path, attr)
  ensures F.GetAttr(I(fs), I(fs'), path, attr)
  {
  }

  lemma RefinesReadLink(fs: P.FileSys, fs': P.FileSys, path: Path, link_path: Path)
  requires PInv.Inv(fs)
  requires P.ReadLink(fs, fs', path, link_path)
  ensures F.ReadLink(I(fs), I(fs'), path, link_path)
  {
  }

  lemma RefinesCreate(fs: P.FileSys, fs': P.FileSys, path: Path, m: MetaData)
  requires PInv.Inv(fs)
  requires P.Create(fs, fs', path, m)
  ensures PInv.Inv(fs')
  ensures F.Create(I(fs), I(fs'), path, m)
  {

    // how to refine create


    // PathExistsEquiv(fs, path);
    // GetMetaEquiv(fs, path);

    assume false;
  }

  lemma RefinesDelete(fs: P.FileSys, fs': P.FileSys, path: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires P.Delete(fs, fs', path, ctime)
  ensures PInv.Inv(fs')
  ensures F.Delete(I(fs), I(fs'), path, ctime)
  {
    assume false;
  }

  lemma RefinesRename(fs: P.FileSys, fs': P.FileSys, source: Path, dest: Path, ctime: Time)
  requires PInv.Inv(fs)
  requires P.Rename(fs, fs', source, dest, ctime)
  ensures PInv.Inv(fs')
  ensures F.Rename(I(fs), I(fs'), source, dest, ctime)
  {
    assume false;
  }

  lemma RefinesLink(fs: P.FileSys, fs': P.FileSys, source: Path, dest: Path, ctime: Time, hiddenName: Option<Path>)
  requires PInv.Inv(fs)
  requires P.Link(fs, fs', source, dest, ctime, hiddenName)
  ensures PInv.Inv(fs')
  ensures F.Link(I(fs), I(fs'), source, dest, ctime)
  {
    assume false;
  }

  // lemma RefinesSimpleStep(fs: P.FileSys, fs': P.FileSys, step: P.Step)
  // requires PInv.Inv(fs)
  // requires P.NextStep(fs, fs', step)
  // requires step.CreateStep? || step.ChangeAttrStep? || step.TruncateStep? || step.WriteStep? || step.UpdateTimeStep?
  // ensures PInv.Inv(fs')
  // ensures F.NextStep(I(fs), I(fs'), IStep(step))
  // {
  //   assume false;
  // }

  // maybe for simple ones

}
