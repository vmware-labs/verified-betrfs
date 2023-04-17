using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.ComponentModel;

namespace Microsoft.Dafny.Linear {

  // TODO(andrea) move/remove
  static class Util {

    internal static void OxideDebug(IToken token, String msg, params object[] args) {
      if (DafnyOptions.O.OxideDebug) {
        Console.ForegroundColor = ConsoleColor.Cyan;
        Console.Error.WriteLine("[oxide] " + ErrorReporter.TokenToString(token).PadRight(20) + " " + String.Format(msg, args));
        Console.ResetColor();
      }
    }

    static public void PrintObject(Object obj) {
        System.Type t = obj.GetType();
        foreach(var fieldInfo in t.GetFields()) {
            Console.WriteLine("[f] {0}={1}", fieldInfo.Name, fieldInfo.GetValue(obj));
        }
        foreach(PropertyDescriptor descriptor in TypeDescriptor.GetProperties(obj))
        {
            string name=descriptor.Name;
            object value;
            try {
                value = descriptor.GetValue(obj);
            } catch (System.Reflection.TargetInvocationException e) {
                if (e.InnerException is NullReferenceException) {
                  value = "<NullReferenceException>";
                } else {
                  value = "<?Exception?>";
                }
            }
            Console.WriteLine("[p] {0}={1}",name,value);
        }
    }

    static public void PrintObjects(Object obj1, Object obj2) {
        System.Type t = obj1.GetType();
        foreach(var fieldInfo in t.GetFields()) {
            var value1 = fieldInfo.GetValue(obj1);
            var value2 = fieldInfo.GetValue(obj2);
            Console.WriteLine("[f] {3} {0} = {1} <> {2}", fieldInfo.Name,
                value1, value2, value1 != null ? (value1.Equals(value2) ? "  " : "!=") : "??");
        }
        foreach(PropertyDescriptor descriptor in TypeDescriptor.GetProperties(obj1))
        {
            string name=descriptor.Name;
            object value1;
            try {
                value1 = descriptor.GetValue(obj1);
            } catch (System.Reflection.TargetInvocationException e) {
                if (e.InnerException is NullReferenceException) {
                  value1 = "<NullReferenceException>";
                } else {
                  value1 = "<?Exception?>";
                }
            }
            object value2;
            try {
                value2 = descriptor.GetValue(obj2);
            } catch (System.Reflection.TargetInvocationException e) {
                if (e.InnerException is NullReferenceException) {
                  value2 = "<NullReferenceException>";
                } else {
                  value2 = "<?Exception?>";
                }
            }
            Console.WriteLine("[p] {3} {0} = {1} <> {2}", name, value1, value2, value1.Equals(value2) ? "  " : "!=");
        }
    }
  }

  internal static class Visit {
    internal static IEnumerable<List<Statement>> AllStatementLists(List<Statement> stmts) {
      foreach (var stmt in stmts) {
        foreach (var ls in AllStatementLists(stmt)) { yield return ls; }
      }

      yield return stmts;
    }

    internal static IEnumerable<List<Statement>> AllStatementLists(Statement stmt) {
      switch (stmt) {
        case BlockStmt bs:
          foreach (var ls in AllStatementLists(bs.Body)) { yield return ls; }
          break;
        case IfStmt ifs:
          foreach (var ls in AllStatementLists(ifs.Thn.Body)) { yield return ls; }
          if (ifs.Els != null) {
            foreach (var ls in AllStatementLists(ifs.Els)) { yield return ls; }
          }
          break;
        case NestedMatchStmt ms:
          foreach (var mc in ms.Cases) {
            foreach (var ls in AllStatementLists(mc.Body)) { yield return ls; }
          }
          if (ms.ResolvedStatement != null) {
            if (ms.ResolvedStatement is MatchStmt resolvedMs) {
              foreach (var mc in resolvedMs.Cases) {
                foreach (var ls in AllStatementLists(mc.Body)) {
                  yield return ls;
                }
              }
            } else if (ms.ResolvedStatement is BlockStmt resolvedBs) {
              foreach (var ls in AllStatementLists(resolvedBs.Body)) { yield return ls; }
            } else if (ms.ResolvedStatement is IfStmt resolvedIs) {
              foreach (var ls in AllStatementLists(resolvedIs)) { yield return ls; }
            } else {
              Contract.Assert(false);  // Did not expect to reach this.  Need to handle more cases.
            }
          }
          break;
        case WhileStmt ws:
          if (ws.Body != null) {
            foreach (var ls in AllStatementLists(ws.Body.Body)) {
              yield return ls;
            }
          }
          break;
        case AtomicStmt atomicBlockStmt:
          foreach (var ls in AllStatementLists(atomicBlockStmt.Body.Body)) {
            yield return ls;
          }
          break;
      }
    }

    static bool memberIsMethod(MemberDecl decl) {
      var m = decl as Method;
      if (m == null) {
        return false;
      }
      return !(
          m is Constructor ||
          m is LeastLemma ||
          m is GreatestLemma ||
          m is Lemma ||
          m is TwoStateLemma);
    }

    internal static IEnumerable<(TopLevelDecl, Method)> AllMethodMembers(ModuleDefinition module) {
      foreach (var decl in module.TopLevelDecls)
      {
        var topLevelDecl = (decl as TopLevelDeclWithMembers);
        if (topLevelDecl != null) {
          foreach (var m in topLevelDecl.Members.Where(memberIsMethod)) {
            var method = (Method) m;
            yield return (topLevelDecl, method);
          }
        }
      }
    }

  }

  public class InoutTranslateRewriter : IRewriter {
    public delegate string FreshTempVarName(string prefix, ICodeContext context);

    FreshTempVarName freshTempVarName;

    public InoutTranslateRewriter(ErrorReporter reporter, FreshTempVarName freshTempVarName) : base(reporter) {
      this.freshTempVarName = freshTempVarName;
    }

    Cloner cloner = new Cloner();

    (Expression, Expression)? DatatypeUpdateExprFor(Expression expr, Expression value) {
      var tok = new AutoGeneratedToken(expr.tok);
      if (expr is ExprDotName) {
        var dotName = (ExprDotName) expr;
        var newValue = new DatatypeUpdateExpr(tok, cloner.CloneExpr(dotName.Lhs),
          new List<Tuple<IToken, string, Expression>> { Tuple.Create((IToken) tok, dotName.SuffixName, value) });
        return DatatypeUpdateExprFor(dotName.Lhs, newValue);
      } else if (expr is NameSegment) {
        return (new IdentifierExpr(tok, ((NameSegment) expr).Name), value);
      } else if (expr is ThisExpr) {
        return null; // (new ThisExpr(tok), value);
      } else {
        reporter.Error(MessageSource.Rewriter, expr.tok, "invalid inout argument");
        return null;
      }
    }

    void PreRewriteMethod(Method m, TopLevelDecl enclosingDecl) {
      Contract.Requires(m != null);
      Util.OxideDebug(m.tok, "Rewriting method {0}", m.Name);
      // TODO(andrea) m.CompileOuts = m.Outs.ToList();
      // TODO(andrea) m.CompileIns = m.Ins.ToList();

      var body = m.Body?.Body;

      void AddGeneratedInoutFormals(Formal f, int insertAt) {
        var fTok = new AutoGeneratedToken(f.tok);

        var outFormal = new Formal(fTok, f.Name, f.Type, false, f.Usage, false, false);
        m.Outs.Add(outFormal);

        var inFormal = new Formal(fTok, "old_" + f.Name, f.Type, false, f.Usage, false, true);
        m.Ins.Insert(insertAt, inFormal);

        if (body != null) {
          var mTok = new AutoGeneratedToken(m.tok);

          var lhs = new IdentifierExpr(mTok, f.Name);
          var rhsNameSegment = new NameSegment(fTok, "old_" + f.Name, null);
          var rhs = new ExprRhs(rhsNameSegment);
          var updateStmt = new UpdateStmt(mTok, mTok,
            new List<Expression> { lhs },
            new List<AssignmentRhs> { rhs });
          updateStmt.AssumeRhsCompilable = false;
          body.Insert(0, updateStmt);
          Util.OxideDebug(updateStmt.Tok, "    {0}", Printer.StatementToString(updateStmt));
        }
      }

      bool signatureRewritten = false;

      for (int i = 0; i < m.Ins.Count; i++) {
        if (m.Ins[i].Inout) {
          var f = m.Ins[i];
          m.Ins.RemoveAt(i);

          AddGeneratedInoutFormals(f, i);
          signatureRewritten = true;
        }
      }

      if (m.HasInoutThis) {
        AddGeneratedInoutFormals(new Formal(new AutoGeneratedToken(m.tok), "self", UserDefinedType.FromTopLevelDecl(m.tok, enclosingDecl), false, m.Usage, false, true), 0);
        // TODO(andrea) DISALLOW "this" in body

        signatureRewritten = true;
      }

      if (signatureRewritten) {
        Util.OxideDebug(m.tok, "  new signature: {0}", Printer.MethodSignatureToString(m));

        if (m.IsGhost) {
          reporter.Error(MessageSource.Rewriter, m.tok, "inout formals not allowed in ghost methods");
        }
      }

      if (body != null) {
        foreach (var stmtList in Visit.AllStatementLists(body)) {
          for (int s = 0; s < stmtList.Count; s++) {
            var stmt = stmtList[s];
            var varDeclStmt = stmt as VarDeclStmt;
            var updStmt = (stmt as UpdateStmt) ?? (varDeclStmt?.Update as UpdateStmt);
            var firstExprRhs = updStmt?.Rhss.First() as ExprRhs;
            var applySuffix = firstExprRhs?.Expr as ApplySuffix;
            if (updStmt != null && updStmt.IsInoutAssign) {
              // inout assignment
              Util.OxideDebug(stmt.Tok, "  rewriting assignment " + Printer.StatementToString(stmt));
              var exprRhs = updStmt.Rhss[0] as ExprRhs;
              if (exprRhs == null) {
                reporter.Error(MessageSource.Rewriter, updStmt, "invalid rhs for inout update statement");
              } else {
                var aTok = new AutoGeneratedToken(stmt.Tok);
                var rhs = cloner.CloneExpr(exprRhs.Expr);
                var varName = freshTempVarName("_inout_tmp_", m);
                var datatypeUpdateFor = DatatypeUpdateExprFor(updStmt.Lhss[0], new IdentifierExpr(aTok, varName));
                if (datatypeUpdateFor.HasValue) {
                  stmtList.RemoveAt(s);
                  var genLocalVar =
                    new LocalVariable(aTok, aTok, varName, new InferredTypeProxy(),
                      updStmt.InoutAssign == InoutAssign.Ghost ? Usage.Ghost : (
                        updStmt.InoutAssign == InoutAssign.Ordinary ? Usage.Ordinary :
                        throw new Exception("invalid InoutAssign")
                      ));
                  var genUpdStmt = new UpdateStmt(aTok, aTok,
                    new List<Expression> { new IdentifierExpr(genLocalVar.Tok, genLocalVar.Name) },
                    new List<AssignmentRhs> { new ExprRhs(rhs) });
                  var genVarDeclStmt = new VarDeclStmt(aTok, aTok, new List<LocalVariable> { genLocalVar }, genUpdStmt);
                  stmtList.Insert(s, genVarDeclStmt);
                  Util.OxideDebug(stmtList[s].Tok, "    " + Printer.StatementToString(stmtList[s]));
                  s++;

                  var (updateLhs, updateExpr) = datatypeUpdateFor.Value;
                  var newExprRhs = new ExprRhs(updateExpr);
                  var newUpdStmt = new UpdateStmt(aTok, aTok,
                    new List<Expression> { updateLhs },
                    new List<AssignmentRhs> { newExprRhs });
                  newUpdStmt.AssumeRhsCompilable = true;
                  newUpdStmt.InoutAssignTarget =
                    (updStmt.InoutAssign == InoutAssign.Ghost ? Usage.Ghost : (
                      (updStmt.InoutAssign == InoutAssign.Ordinary ? Usage.Ordinary :
                      throw new Exception("invalid InoutAssign"))
                    ), updStmt.Lhss[0]);
                  stmtList.Insert(s, newUpdStmt);
                  Util.OxideDebug(stmtList[s].Tok, " -> " + Printer.StatementToString(stmtList[s]));
                }
              }
            } else if (applySuffix != null && !updStmt.IsInoutAssign) {
              var inoutArgs = applySuffix.Args.Where(a => a.Inout).ToList();
              if (inoutArgs.Count == 0 && !firstExprRhs.InoutThis) {
                continue;
              }

              // TODO(andrea)
              if (firstExprRhs.InoutThis) {
                Util.OxideDebug(stmt.Tok, "  rewriting " + Printer.StatementToString(stmt) + " (inout this)");
              } else {
                Util.OxideDebug(stmt.Tok, "  rewriting " + Printer.StatementToString(stmt));
              }

              if (firstExprRhs.InoutThis) {
                var dotNameMethod = applySuffix.Lhs as ExprDotName;
                if (dotNameMethod == null) {
                  reporter.Error(MessageSource.Rewriter, applySuffix, "invalid inout call");
                  return;
                }
                Expression selfArg = cloner.CloneExpr(((ExprDotName) applySuffix.Lhs).Lhs);
                var selfApplySuffixArg = new ApplySuffixArg { Expr = selfArg, Inout = true };
                applySuffix.Args.Insert(0, selfApplySuffixArg);
                applySuffix.RewrittenAsInoutThis = true;
                inoutArgs.Add(selfApplySuffixArg);
              }

              var updatedFields = inoutArgs.ConvertAll(a => {
                var aTok = new AutoGeneratedToken(a.Expr.tok);
                var varName = freshTempVarName("_inout_tmp_", m);
                var datatypeUpdateFor = DatatypeUpdateExprFor(a.Expr, new IdentifierExpr(aTok, varName));
                // TODO(andrea)
                UpdateStmt updateStmt = null;
                if (datatypeUpdateFor.HasValue) {
                  var (updateLhs, updateExpr) = datatypeUpdateFor.Value;
                  updateStmt = new UpdateStmt(aTok, aTok,
                    new List<Expression> { updateLhs },
                    new List<AssignmentRhs> { new ExprRhs(updateExpr) });
                  updateStmt.AssumeRhsCompilable = true;
                  Util.OxideDebug(a.Expr.tok, "    varName: " + varName + ", " + Printer.ExprToString(a.Expr) + ", " + Printer.ExprToString(updateExpr));
                }
                return (
                  new LocalVariable(aTok, aTok, varName, new InferredTypeProxy(), Usage.Ignore), updateStmt);
              });
              var tempLocalVars = updatedFields.Select(x => x.Item1).ToList();
              foreach (var tv in tempLocalVars) {
                updStmt.Lhss.Add(new IdentifierExpr(tv.Tok, tv.Name));
              }
              if (varDeclStmt == null) {
                var asTok = new AutoGeneratedToken(applySuffix.tok);
                varDeclStmt = new VarDeclStmt(asTok, asTok, tempLocalVars, null);
                stmtList.Insert(s, varDeclStmt);
                // TODO(andrea)
                Util.OxideDebug(stmtList[s].Tok, "    " + Printer.StatementToString(stmtList[s]));
                s++;
              } else {
                varDeclStmt.Locals.AddRange(tempLocalVars);
                // TODO(andrea)
                Util.OxideDebug(stmtList[s].Tok, "    " + Printer.StatementToString(stmtList[s]));
              }
              varDeclStmt.InoutRewrittenArgs = updatedFields.Count;
              Util.OxideDebug(stmt.Tok, "    " + Printer.StatementToString(stmt));
              foreach (var newUpdStmt in updatedFields.Select(x => x.Item2)) {
                if (newUpdStmt != null) {
                  s++;
                  stmtList.Insert(s, newUpdStmt);
                  Util.OxideDebug(stmtList[s].Tok, "    " + Printer.StatementToString(stmtList[s]));
                }
              }
            } else if (firstExprRhs?.InoutThis ?? false) {
              reporter.Error(MessageSource.Rewriter, firstExprRhs.Tok, "inout not allowed here");
            } else if (updStmt?.IsInoutAssign ?? false) {
              reporter.Error(MessageSource.Rewriter, stmt.Tok, "invalid inout update");
            }
          }
        }
      }
    }

    internal override void PreResolve(ModuleDefinition module) {
      foreach (var (tld, method) in Visit.AllMethodMembers(module)) {
        PreRewriteMethod(method, tld);
      }
    }
  }

  static class OxideCompilationRewriter {
    public static void Rewrite(ModuleDefinition module) {
      foreach (var (tld, method) in Visit.AllMethodMembers(module)) {
        Util.OxideDebug(method.tok, "Rewriting method for compilation {0}", method.Name);

        if (method.HasInoutThis) {
          method.Ins.RemoveAt(0);
          method.Outs.RemoveAt(method.Outs.Count - 1);
        }

        var inoutInArgs = method.Ins.Select((formal, inPos) => new { inPos, formal }).Where(x => x.formal.Inout).Select((x, outPos) => new { inPos = x.inPos, outPos }).ToList();
        var inoutArgCount = inoutInArgs.Count;
        var inoutOutArgs = method.Outs.GetRange(method.Outs.Count - inoutArgCount, inoutArgCount);
        method.Outs.RemoveRange(method.Outs.Count - inoutArgCount, inoutArgCount);
        const String oldPrefix = "old_";
        foreach (var a in inoutInArgs) {
          var arg = method.Ins[a.inPos];
          Contract.Assert(arg.Name.StartsWith(oldPrefix));
          var inoutArg = inoutOutArgs[a.outPos];
          inoutArg.Inout = true;
          method.Ins[a.inPos] = inoutArg;
        }
        if (inoutArgCount > 0) {
          method.Req.Clear();
          method.Ens.Clear();
        }
        Util.OxideDebug(method.tok, "  {0}", Printer.MethodSignatureToString(method));

        var body = method.Body?.Body;
        if (body != null) {
          if (method.HasInoutThis) {
            Util.OxideDebug(body[0].Tok, "  removing {0}", Printer.StatementToString(body[0]));
            body.RemoveRange(0, 1);
          }
          for (int i = 0; i < inoutArgCount; i++) {
            Util.OxideDebug(body[i].Tok, "  removing {0}", Printer.StatementToString(body[i]));
          }
          body.RemoveRange(0, inoutArgCount);

          foreach (var stmtList in Visit.AllStatementLists(body)) {
            for (int s = 0; s < stmtList.Count; s++) {
              var stmt = stmtList[s];
              var updStmt = stmt as UpdateStmt;
              var varDeclStmt = stmt as VarDeclStmt;
              if (updStmt != null && updStmt.AssumeRhsCompilable && updStmt.InoutAssignTarget.HasValue) {
                var (usage, targetExpr) = updStmt.InoutAssignTarget.Value;
                var debugTargetExpr = Printer.ExprToString(targetExpr);
                var debugRhs = Printer.ExprToString(((ExprRhs) updStmt.Rhss[0]).Expr).Contains("lseq_take_inout");
                Util.OxideDebug(stmtList[s - 1].Tok, "  (assign) removing {0}", Printer.StatementToString(stmtList[s - 1]));
                var innerUpdStmt = (UpdateStmt) ((VarDeclStmt) stmtList[s - 1]).Update;
                var rhs = (ExprRhs) innerUpdStmt.Rhss[0];
                Contract.Assert(innerUpdStmt.ResolvedStatements.Count == 1);
                var resolvedRhs = innerUpdStmt.ResolvedStatements[0];
                stmtList.RemoveAt(s - 1);
                s--;
                Util.OxideDebug(stmtList[s].Tok, "  (assign) {0} has target {1}, rhs {2}",
                  Printer.StatementToString(stmtList[s]), Printer.ExprToString(targetExpr), Printer.ExprToString(rhs.Expr));
                updStmt.Lhss.Clear();
                updStmt.Lhss.Add(targetExpr);
                updStmt.Rhss.Clear();
                updStmt.Rhss.Add(rhs);
                updStmt.InoutAssign = usage.IsOrdinaryKind ? InoutAssign.Ordinary : (
                  usage.IsGhostKind ? InoutAssign.Ghost :
                  throw new Exception("invalid InoutAssignUsage"));
                var generatedTok = new AutoGeneratedToken(stmtList[s].Tok);
                Contract.Assert(updStmt.ResolvedStatements.Count == 1);
                updStmt.ResolvedStatements.Clear();
                if (resolvedRhs is CallStmt callStmt) {
                  var resolvedCallStmt = new CallStmt(generatedTok, generatedTok, new List<Expression> { targetExpr.Resolved }, callStmt.MethodSelect, callStmt.Args);
                  updStmt.ResolvedStatements.Add(resolvedCallStmt);
                } else {
                  var resolvedAssignStmt = new AssignStmt(generatedTok, generatedTok, targetExpr.Resolved, rhs);
                  updStmt.ResolvedStatements.Add(resolvedAssignStmt);
                }

                Util.OxideDebug(stmtList[s].Tok, "  (assign)   rewritten as {0} ({1})",
                  Printer.StatementToString(stmtList[s]), updStmt.InoutAssign);
              } else if (varDeclStmt != null && varDeclStmt.InoutRewrittenArgs.HasValue) {
                var argCount = varDeclStmt.InoutRewrittenArgs.Value;
                Util.OxideDebug(stmtList[s].Tok, "  (apply) undoing rewrite for {0} args starting {1} (inline update {2})",
                  argCount, Printer.StatementToString(stmtList[s]), varDeclStmt.Update != null ? "present" : "absent");

                void RewriteAUpdateStmt(UpdateStmt updateStmt) {
                  var exprRhs = (ExprRhs)updateStmt.Rhss[0];
                  var debugRhs = Printer.ExprToString(exprRhs.Expr).Contains("lseq_take_inout");
                  var applySuffix = exprRhs.Expr as ApplySuffix;
                  if (applySuffix != null && applySuffix.RewrittenAsInoutThis) {
                    Contract.Assert(updateStmt.Rhss.Count == 1);
                    applySuffix.Args.RemoveAt(0);
                    exprRhs.Expr.Inout = true;
                  }
                  if (updateStmt.ResolvedStatements.Count == 1) {
                    var resolvedCallStmt = (CallStmt)updateStmt.ResolvedStatements[0];
                    resolvedCallStmt.Lhs.RemoveRange(resolvedCallStmt.Lhs.Count - argCount, argCount);
                  } else {
                    // TODO(andrea) should this case ever happen?
                    Util.OxideDebug(stmtList[s].Tok, "  (apply)   DEBUG no resolved statement for {0}", Printer.StatementToString(updateStmt));
                  }
                }

                if (varDeclStmt.Update == null) {
                  Util.OxideDebug(stmtList[s].Tok, "  (apply) removing {0}", Printer.StatementToString(stmtList[s]));
                  stmtList.RemoveAt(s);
                  var updateStmt = (UpdateStmt) stmtList[s];
                  updateStmt.Lhss.RemoveRange(updateStmt.Lhss.Count - argCount, argCount);
                  RewriteAUpdateStmt(updateStmt);
                  Util.OxideDebug(stmtList[s].Tok, "  (apply)   rewritten (a) as {0}", Printer.StatementToString(stmtList[s]));
                } else {
                  varDeclStmt.Locals.RemoveRange(varDeclStmt.Locals.Count - argCount, argCount);
                  varDeclStmt.Update.Lhss.RemoveRange(varDeclStmt.Update.Lhss.Count - argCount, argCount);
                  // TODO(andrea) deduplicate
                  var updateStmt = (UpdateStmt)varDeclStmt.Update;
                  RewriteAUpdateStmt(updateStmt);
                  Util.OxideDebug(stmtList[s].Tok, "  (apply)   rewritten (b) as {0}", Printer.StatementToString(stmtList[s]));
                }
                for (int c = 0; c < argCount; ++c) {
                  Util.OxideDebug(stmtList[s + 1].Tok, "  (apply)   removing {0}", Printer.StatementToString(stmtList[s + 1]));
                  stmtList.RemoveAt(s + 1);
                }
              }
            }
          }
        }
      }

    }
  }
}
