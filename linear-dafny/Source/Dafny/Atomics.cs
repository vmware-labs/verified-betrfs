using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Linear
{
    internal class PreservedContents
    {
        public readonly String Atomic;
        public readonly String NewValue;

        public PreservedContents(String atomic, String newValue)
        {
            this.Atomic = atomic;
            this.NewValue = newValue;
        }
    }

    internal class BlockOpen
    {
        public readonly PreservedContents preservedContents;
        public readonly CallStmt stmt;

        public BlockOpen(PreservedContents preservedContents, CallStmt stmt)
        {
            this.preservedContents = preservedContents;
            this.stmt = stmt;
        }
    }
    
    public class AtomicRewriter : IRewriter
    {
        internal override void PreResolve(ModuleDefinition module)
        {
            foreach (var (_, method) in Visit.AllMethodMembers(module))
            {
                AtomicBlockTranslator abt = new AtomicBlockTranslator(reporter, freshTempVarName, method);
                var body = method.Body?.Body;
                if (body != null)
                {
                    abt.VisitStatementList(body);
                }
            }

            DefaultClassDecl defaultClassDecl = null;
            foreach (var decl in module.TopLevelDecls)
            {
                if (decl is DefaultClassDecl dc)
                {
                    defaultClassDecl = dc;
                }
            }
            
            foreach (var decl in module.TopLevelDecls)
            {
                if (decl is IndDatatypeDecl datatypeDecl)
                {
                    HandleFoldDatatype(datatypeDecl, defaultClassDecl);
                }
            }
        }

        private Expression defn_call(IToken tok, string id)
        {
            return new ApplySuffix(tok, null, new ExprDotName(
                tok,
                new NameSegment(tok, id, null),
                "defn",
                null
            ), new List<ApplySuffixArg>());
        }

        void HandleFoldDatatype(IndDatatypeDecl decl, DefaultClassDecl defaultClassDecl)
        {
            if (!Attributes.Contains(decl.Attributes, "glinear_fold"))
            {
                return;
            }

            var tok = decl.tok;

            if (!decl.Usage.IsOrdinaryKind)
            {
                reporter.Error(MessageSource.Rewriter, tok,
                    "glinear_fold feature may only be used on an ordinary datatype");
                return;
            }

            if (decl.TypeArgs.Count > 0)
            {
                reporter.Error(MessageSource.Rewriter, tok,
                    "glinear_fold is currently not supported with type parameters");
                return;
            }

            Type aType = new UserDefinedType(tok, decl.Name, null);

            Type bType = null;
            foreach (MemberDecl member in decl.Members)
            {
                if (member is Function f && member.Name == "defn")
                {
                    if (f.Formals.Count != 0)
                    {
                        reporter.Error(MessageSource.Rewriter, tok,
                            "defn should take no additional parameters");
                        return;
                    }

                    if (f.Req.Count != 0)
                    {
                        reporter.Error(MessageSource.Rewriter, tok,
                            "defn should have no requires clauses");
                        return;
                    }

                    bType = f.ResultType;
                }
            }

            if (bType == null)
            {
                reporter.Error(MessageSource.Rewriter, tok,
                    "defn function not found");
                return;
            }

            var cloner = new Cloner();

            var foldFunc = new Function(
                tok,
                decl.Name + "_fold",
                false,
                Usage.Ordinary,
                new List<TypeParameter>(),
                new List<Formal>()
                {
                    new Formal(tok, "a", cloner.CloneType(aType), true, Usage.Ghost),
                    new Formal(tok, "b", cloner.CloneType(bType), true, Usage.Linear(LinearRealm.Erased))
                },
                new Formal(tok, "a'", cloner.CloneType(aType), false, Usage.Linear(LinearRealm.Erased)),
                cloner.CloneType(aType),
                new List<AttributedExpression>() {
                    new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, 
                        defn_call(tok, "a"),
                        new NameSegment(tok, "b", null)
                        ))
                    },
                new List<FrameExpression>(),
                new List<AttributedExpression>() {
                    new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, 
                        new NameSegment(tok, "a'", null),
                        new NameSegment(tok, "a", null)
                    ))
                },
                new Specification<Expression>(new List<Expression>(), null),
                null,
                new Attributes("extern", new List<Expression>(), null),
                null
            );
            
            var unfoldFunc = new Function(
                tok,
                decl.Name + "_unfold",
                false,
                Usage.Ordinary,
                new List<TypeParameter>(),
                new List<Formal>()
                {
                    new Formal(tok, "a", cloner.CloneType(aType), true, Usage.Linear(LinearRealm.Erased))
                },
                new Formal(tok, "b", cloner.CloneType(bType), false, Usage.Linear(LinearRealm.Erased)),
                cloner.CloneType(bType),
                new List<AttributedExpression>(),
                new List<FrameExpression>(),
                new List<AttributedExpression>() {
                    new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, 
                        defn_call(tok, "a"),
                        new NameSegment(tok, "b", null)
                    ))
                },
                new Specification<Expression>(new List<Expression>(), null),
                null,
                new Attributes("extern", new List<Expression>(), null),
                null
            );
            
            var unfoldBorrowFunc = new Function(
                tok,
                decl.Name + "_unfold_borrow",
                false,
                Usage.Ordinary,
                new List<TypeParameter>(),
                new List<Formal>()
                {
                    new Formal(tok, "a", cloner.CloneType(aType), true, Usage.Shared(LinearRealm.Erased))
                },
                new Formal(tok, "b", cloner.CloneType(bType), false, Usage.Shared(LinearRealm.Erased)),
                cloner.CloneType(bType),
                new List<AttributedExpression>(),
                new List<FrameExpression>(),
                new List<AttributedExpression>() {
                    new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, 
                        defn_call(tok, "a"),
                        new NameSegment(tok, "b", null)
                    ))
                },
                new Specification<Expression>(new List<Expression>(), null),
                null,
                new Attributes("extern", new List<Expression>(), null),
                null
            );

            foldFunc.InheritVisibility(decl, true);
            unfoldFunc.InheritVisibility(decl, true);
            unfoldBorrowFunc.InheritVisibility(decl, true);
            
            defaultClassDecl.Members.Add(foldFunc);
            defaultClassDecl.Members.Add(unfoldFunc);
            defaultClassDecl.Members.Add(unfoldBorrowFunc);
        }
    
        
        internal override void PostResolve(ModuleDefinition module)
        {
            foreach (var (_, method) in Visit.AllMethodMembers(module))
            {
                Validate(method);
            }
        }

        private const String EXECUTE_PREFIX = "execute__atomic__";
        private const String FINISH_NAME = "finish__atomic";
        private const String EXECUTE_NAME_NOOP = "execute__atomic__noop";

        private bool is_open_stmt(CallStmt call)
        {
            var name = call.Method.CompileName;
            var parts = name.Split(".");
            return parts[^1].StartsWith(EXECUTE_PREFIX);
        }

        private bool is_close_stmt(CallStmt call)
        {
            var name = call.Method.CompileName;
            var parts = name.Split(".");
            return parts[^1] == FINISH_NAME;
        }

        private bool is_open_call_entirely_ghost(CallStmt call)
        {
            var name = call.Method.CompileName;
            var parts = name.Split(".");
            return parts[^1] == EXECUTE_NAME_NOOP;
        }

        /*private void check_names_match(IToken tok, String s1, String s2)
        {
            var parts = s1.Split(".");
            Contract.Assert(parts[^1].StartsWith(EXECUTE_PREFIX));
            var newName = parts[^1].Substring(EXECUTE_PREFIX.Length);
            parts[^1] = FINISH_PREFIX + newName;
            var expectedCloseName = String.Join(".", parts);
            
            if (expectedCloseName != s2)
            {
                reporter.Error(MessageSource.Rewriter, tok,
                    "Improper atomic statement nesting: close and open don't match");
            }
        }*/

        private void check_open_close_match(
                    CallStmt openStmt,
                    CallStmt closeStmt,
                    PreservedContents openPreservedContents)
        {
            //var call1 = openStmt;
            //var call2 = closeStmt;
            //check_names_match(openStmt.Tok, call1.Method.CompileName, call2.Method.CompileName);

            PreservedContents closedPreservedContents = get_preserved_contents_close_stmt(closeStmt);

            if (openPreservedContents.Atomic != null
                && closedPreservedContents.Atomic != null
                && openPreservedContents.Atomic != closedPreservedContents.Atomic)
            {
                reporter.Error(MessageSource.Rewriter, closeStmt.Tok,
                    "Improper atomic statement nesting: 'atomic' field does not match: got '{0}' and '{1}'",
                    openPreservedContents.Atomic,
                    closedPreservedContents.Atomic);
            }
            
            if (openPreservedContents.NewValue != null
                && closedPreservedContents.NewValue != null
                && openPreservedContents.NewValue != closedPreservedContents.NewValue)
            {
                reporter.Error(MessageSource.Rewriter, closeStmt.Tok,
                    "Improper atomic statement nesting: 'new_value' field does not match: got '{0}' and '{1}'",
                    openPreservedContents.NewValue,
                    closedPreservedContents.NewValue);
            }
        }

        private String call_get_arg(CallStmt call, int i)
        {
            if (i >= call.Args.Count)
            {
                reporter.Error(MessageSource.Rewriter, call.Tok,
                    "Atomic checking: can't get arg of stmt: not enough args");
                return null;
            }
            else
            {
                var arg = call.Args[i].Expr;
                if (arg is NameSegment ns)
                {
                    if (ns.Resolved is IdentifierExpr id)
                    {
                        return id.Var.CompileName;
                    }
                }
                reporter.Error(MessageSource.Rewriter, call.Tok,
                    "Atomic checking: can't get arg of stmt: not an IdentifierExpr");
                return null;
            }
        }
        
        private String call_get_out_arg(CallStmt call, int i)
        {
            if (i >= call.Lhs.Count)
            {
                reporter.Error(MessageSource.Rewriter, call.Tok,
                    "Atomic checking: can't get out arg of stmt: not enough args");
                return null;
            }
            else
            {
                var arg = call.Lhs[i];
                if (arg is IdentifierExpr id)
                {
                    return id.Var.CompileName;
                }
                else
                {
                    reporter.Error(MessageSource.Rewriter, call.Tok,
                        "Atomic checking: can't get out arg of stmt: not an IdentifierExpr");
                    return null;
                }
            }
        }

        private PreservedContents get_preserved_contents_open_stmt(CallStmt openStmt)
        {
            return new PreservedContents(
                call_get_arg(openStmt, 0),
                call_get_out_arg(openStmt, 2));
        }
        
        private PreservedContents get_preserved_contents_close_stmt(CallStmt closeStmt)
        {
            return new PreservedContents(
                call_get_arg(closeStmt, 0),
                call_get_arg(closeStmt, 1));
        }

        private static CallStmt as_call_stmt(Statement stmt)
        {
            if (stmt is VarDeclStmt vds)
            {
                var cus = vds.Update;
                if (cus is UpdateStmt us)
                {
                    if (us.SubStatements.Count() == 1)
                    {
                        var sub = us.SubStatements.First();
                        if (sub is CallStmt cs)
                        {
                            return cs;
                        }
                    }
                }
            } else if (stmt is UpdateStmt us)
            {
                if (us.SubStatements.Count() == 1)
                {
                    var sub = us.SubStatements.First();
                    if (sub is CallStmt cs)
                    {
                        return cs;
                    }
                }
            } else if (stmt is CallStmt cs)
            {
                return cs;
            }

            return null;
        }

        private void check_no_assign_lhs(Expression lhs, String varName)
        {
            switch (lhs)
            {
                case NameSegment ns:
                    check_no_assign_lhs(ns.Resolved, varName);
                    break;
                case IdentifierExpr ie:
                    if (ie.Var != null && ie.Var.CompileName == varName)
                    {
                        reporter.Error(MessageSource.Rewriter, lhs.tok,
                            "Assign to variable which should be preserved for atomic block");
                    }

                    break;
                default:
                    Contract.Assert(false);
                    break;
            }
        }

        private void check_no_assign_stmt(Statement stmt, String varName)
        {
            if (stmt is UpdateStmt us)
            {
                foreach (Expression lhs in us.Lhss)
                {
                    check_no_assign_lhs(lhs, varName);
                }
            }
        }

        private void check_no_assign(Statement stmt, String varName)
        {
            check_no_assign_stmt(stmt, varName);
            foreach (var stmtList in Visit.AllStatementLists(stmt))
            {
                foreach (var s in stmtList)
                {
                    check_no_assign_stmt(s, varName);
                }
            }
        }

        private static bool IsIgnoredVarDecl(Statement stmt)
        {
            if (stmt is VarDeclStmt vds)
            {
                foreach (var local in vds.Locals)
                {
                    if (!(local.Usage.IsLinearOrSharedErased || local.Usage.IsGhostKind) && !local.Usage.ignore)
                    {
                        return false;
                    }
                }
                return vds.Update == null;
            }
            else
            {
                return false;
            }
        }

        public static bool IsGlinearStmt(Statement stmt)
        {
            var callStmt = as_call_stmt(stmt);
            if (callStmt != null)
            {
                var u = callStmt.Method.Usage;
                return ((u.IsLinearKind || u.IsSharedKind) && u.realm == LinearRealm.Erased && callStmt.Method.IsStatic);
            }

            if (stmt is VarDeclStmt vds)
            {
                foreach (var local in vds.Locals)
                {
                    if (!(local.Usage.IsLinearOrSharedErased || local.Usage.IsGhostKind))
                    {
                        return false;
                    }
                }
                return vds.Update == null || IsGlinearStmt(vds.Update);
            } else if (stmt is UpdateStmt us)
            {
                foreach (Statement sub in us.SubStatements)
                {
                    if (!IsGlinearStmt(sub))
                    {
                        return false;
                    }
                }

                return true;
            } else if (stmt is AssignStmt ast)
            {
                if (ast.Lhs is IdentifierExpr ie)
                {
                    var u = ie.Var.Usage;
                    return (u.IsLinearKind || u.IsSharedKind) && u.realm == LinearRealm.Erased;
                }

                return false;
            } else if (stmt is NestedMatchStmt nms)
            {
                var u = nms.Usage;
                return (u.IsLinearKind || u.IsSharedKind) && u.realm == LinearRealm.Erased;
            } else if (stmt is VarDeclPattern vdp)
            {
                foreach (var local in vdp.LocalVars)
                {
                    var u = vdp.Usage;
                    if (!u.IsGhostKind && !(
                        (u.IsLinearKind || u.IsSharedKind) && u.realm == LinearRealm.Erased))
                    {
                        return false;
                    }
                }

                return true;
            }

            return false;
        }

        private String get_id_of_namespace_call(Expression e)
        {
            if (e is ApplySuffix appsuff)
            {
                if (appsuff.ResolvedExpression is FunctionCallExpr fce)
                {
                    if (fce.Name == "namespace")
                    {
                        if (fce.Receiver is NameSegment ns)
                        {
                            if (ns.Resolved is IdentifierExpr ie)
                            {
                                return ie.Var.CompileName;
                            }
                        }
                    }
                }
            }

            return null;
        }

        private bool is_correct_not_equals_assertion(Statement stmt, String expected_id1, String expected_id2)
        {
            Expression expr;
            if (stmt is AssertStmt assert_stmt)
            {
                expr = assert_stmt.Expr;
            }
            else if (stmt is AssumeStmt assume_stmt)
            {
                expr = assume_stmt.Expr;
            }
            else
            {
                return false;
            }

            if (expr is BinaryExpr be)
            {
                if (be.Op == BinaryExpr.Opcode.Neq)
                {
                    String actualId1 = get_id_of_namespace_call(be.E0);
                    String actualId2 = get_id_of_namespace_call(be.E1);
                    
                    Contract.Assert(expected_id1 != null);
                    Contract.Assert(expected_id2 != null);

                    return (actualId1 == expected_id1 && actualId2 == expected_id2)
                           || (actualId1 == expected_id2 && actualId2 == expected_id1);

                }
            }
            return false;
        }
        
        private void Validate(Method m) {
            var body = m.Body?.Body;
            if (body == null)
            {
                return;
            }
            foreach (var stmtList in Visit.AllStatementLists(body))
            {
                List<BlockOpen> openBlocks = new List<BlockOpen>();

                for (int stmtListIndex = 0; stmtListIndex < stmtList.Count; stmtListIndex++)
                {
                    var stmt = stmtList[stmtListIndex];

                    CallStmt call = as_call_stmt(stmt);
                    if (call != null && is_open_stmt(call))
                    {
                        if (openBlocks.Count > 0 && !is_open_call_entirely_ghost(call))
                        {
                            reporter.Error(MessageSource.Rewriter, stmt.Tok,
                                "Improper atomic statement nesting: non-ghost open within another open");
                        }

                        var openStmt = call;
                        var preservedContents = get_preserved_contents_open_stmt(call);
                        
                        foreach (BlockOpen bo in openBlocks)
                        {
                            check_no_assign(openStmt, bo.preservedContents.Atomic);
                            check_no_assign(openStmt, bo.preservedContents.Atomic);
                        }
                        check_no_assign(openStmt, preservedContents.Atomic);

                        for (int j = 0; j < openBlocks.Count; j++)
                        {
                            int sIndex = stmtListIndex - openBlocks.Count + j;
                            if (!(sIndex >= 0 && is_correct_not_equals_assertion(stmtList[sIndex],
                                preservedContents.Atomic, openBlocks[j].preservedContents.Atomic)))
                            {
                                reporter.Error(MessageSource.Rewriter, stmt.Tok,
                                    "Need to assert that ({0}.namespace() != {1}.namespace())",
                                    preservedContents.Atomic, openBlocks[j].preservedContents.Atomic);
                            }
                        }
                        
                        openBlocks.Add(new BlockOpen(preservedContents, openStmt));
                    }
                    else if (call != null && is_close_stmt(call))
                    {
                        if (openBlocks.Count == 0)
                        {
                            reporter.Error(MessageSource.Rewriter, stmt.Tok,
                                "Improper atomic statement nesting: close without corresponding open");
                        }
                        else
                        {
                            var last = openBlocks[^ 1];
                            check_open_close_match(last.stmt, call, last.preservedContents);
                            openBlocks.RemoveAt(openBlocks.Count - 1);
                        }
                    }
                    else
                    {
                        if (openBlocks.Count > 0)
                        {
                            if (!stmt.IsGhost && !IsGlinearStmt(stmt) && !IsIgnoredVarDecl(stmt))
                            {
                                reporter.Error(MessageSource.Rewriter, stmt.Tok,
                                    "Only ghost statements can be within an atomic block");
                            }
                            
                            foreach (BlockOpen bo in openBlocks) {
                                check_no_assign(stmt, bo.preservedContents.Atomic);
                                check_no_assign(stmt, bo.preservedContents.NewValue);
                            }
                        }
                    }
                }

                if (openBlocks.Count > 0)
                {
                    reporter.Error(MessageSource.Rewriter, m.Body.Tok,
                        "block ends with an atomic block open");
                }
            }
        }

        private class AtomicBlockTranslator
        {
            private List<string> atomicVarStack;
                
            private Expression get_release_stmt_expression(AtomicStmt atomicStmt, out ReleaseStmt releaseStmt)
            {
                var body = atomicStmt.Body.Body;
                if (body.Count > 0 && body[^1] is ReleaseStmt rs)
                {
                    releaseStmt = rs;
                    return rs.E;
                }
                else
                {
                    releaseStmt = null;
                    return null;
                }
            }
            
            private string get_acquire_stmt_var_name(AtomicStmt atomicStmt)
            {
                var body = atomicStmt.Body.Body;
                if (body.Count > 0 && body[0] is AcquireStmt acquireStmt)
                {
                    return acquireStmt.Id.val;
                }
                else
                {
                    return null;
                }
            }

            private List<Statement> get_inner_stmts(AtomicStmt atomicStmt)
            {
                var body = atomicStmt.Body.Body;
                List<Statement> newStmts = new List<Statement>();
                for (int i = 0; i < body.Count; i++)
                {
                    if (i == 0 && body[i] is AcquireStmt) continue;
                    if (i == body.Count - 1 && body[i] is ReleaseStmt) continue;
                    newStmts.Add(body[i]);
                }

                return newStmts;
            }

            private Statement var_decl_empty(IToken tok, string id)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Ordinary)
                }, null);
            }
            
            private Statement var_decl(IToken tok, string id, Expression e)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Ordinary)
                }, new UpdateStmt(tok, tok, 
                    new List<Expression>() {new AutoGhostIdentifierExpr(tok, id)},
                    new List<AssignmentRhs>() {new ExprRhs(e)}));
            }

            private Statement shared_var_decl(IToken tok, string id, Expression e)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Shared(LinearRealm.Physical))
                }, new UpdateStmt(tok, tok, 
                    new List<Expression>() {new AutoGhostIdentifierExpr(tok, id)},
                    new List<AssignmentRhs>() {new ExprRhs(e)}));
            }
            
            private Statement gshared_var_decl(IToken tok, string id, Expression e)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Shared(LinearRealm.Erased))
                }, new UpdateStmt(tok, tok, 
                    new List<Expression>() {new AutoGhostIdentifierExpr(tok, id)},
                    new List<AssignmentRhs>() {new ExprRhs(e)}));
            }

            private Statement ghost_var_decl_empty(IToken tok, string id)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Ghost)
                }, null);
            }
            
            private Statement ghost_var_decl(IToken tok, string id, Expression e)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Ghost)
                }, new UpdateStmt(tok, tok, 
                    new List<Expression>() {new IdentifierExpr(tok, id)},
                    new List<AssignmentRhs>() {new ExprRhs(e)}));
            }
            
            private Statement glinear_var_decl_empty(IToken tok, string id)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Linear(LinearRealm.Erased))
                }, null);
            }
            
            private Statement glinear_var_decl(IToken tok, string id, Expression e)
            {
                return new VarDeclStmt(tok, tok, new List<LocalVariable>()
                {
                    new LocalVariable(tok, tok, id, new InferredTypeProxy(), Usage.Linear(LinearRealm.Erased))
                }, new UpdateStmt(tok, tok, 
                    new List<Expression>() {new IdentifierExpr(tok, id)},
                    new List<AssignmentRhs>() {new ExprRhs(e)}));
            }

            private Expression GetFinishAtomicExpr(Expression openExpr)
            {
                if (openExpr is NameSegment ns)
                {
                    return new NameSegment(openExpr.tok, "finish_atomic", null);
                }
                else
                {
                    Contract.Assert(false);
                    return null;
                }
            }
            
            private bool IsAtomicNoop(Expression openExpr)
            {
                if (openExpr is NameSegment ns)
                {
                    return ns.Name == "execute_atomic_noop";
                }
                else
                {
                    Contract.Assert(false);
                    return false;
                }
            }
            
            private bool IsReturnValueGhost(Expression openExpr)
            {
                if (openExpr is NameSegment ns)
                {
                    return ns.Name == "execute_atomic_noop"
                           || ns.Name == "execute_atomic_store";
                }
                else
                {
                    Contract.Assert(false);
                    return false;
                }
            }

            private Expression namespace_call(IToken tok, string id)
            {
                return new ApplySuffix(tok, null, new ExprDotName(
                    tok,
                    new NameSegment(tok, id, null),
                    "namespace",
                    null
                ), new List<ApplySuffixArg>());
            }
            
            private List<Statement> GetNewStmtList(AtomicStmt atomicStmt)
            {
                string acquireStmtVarName = get_acquire_stmt_var_name(atomicStmt);
                ReleaseStmt releaseStmt;
                Expression releaseStmtExpr = get_release_stmt_expression(atomicStmt, out releaseStmt);

                if (acquireStmtVarName == null && releaseStmtExpr != null)
                {
                    reporter.Error(MessageSource.Rewriter, atomicStmt.Tok,
                        "Atomic block has 'release' statement but no 'acquire' statement");
                    return new List<Statement>();
                }
                if (acquireStmtVarName != null && releaseStmtExpr == null)
                {
                    reporter.Error(MessageSource.Rewriter, atomicStmt.Tok,
                        "Atomic block has 'acquire' statement but no 'release' statement");
                    return new List<Statement>();
                }

                if (!(atomicStmt.Call is ApplySuffix))
                {
                    reporter.Error(MessageSource.Rewriter, atomicStmt.Call.tok,
                        "Atomic statement expects a call expressions");
                    return new List<Statement>();
                }

                var applySuffix = (ApplySuffix) atomicStmt.Call;

                if (applySuffix.Args.Count == 0)
                {
                    reporter.Error(MessageSource.Rewriter, atomicStmt.Call.tok,
                        "Atomic statement expects a call expression with at least 1 argument");
                    return new List<Statement>();
                }

                var atomicAsa = applySuffix.Args[0];
                var atomicExpr = atomicAsa.Expr;

                if (atomicAsa.Inout)
                {
                    reporter.Error(MessageSource.Rewriter, atomicStmt.Call.tok,
                        "Atomic statement argument 0: inout not expected");
                    return new List<Statement>();
                }
                
                // atomic return_value := atomic_fn(atomic, args...) {
                //      acquire g;
                //      ...
                //      release g_expr;
                // }
                //
                // should be turned into
                //
                // shared var atomic_value := atomic;
                // var return_value;
                // ghost var old_value;
                // ghost var new_value;
                // glinear var g;
                // ghost var dummy_bool := true;
                // return_value, old_value, new_value, g := atomic_fn(atomic_value, args...);
                // if dummy_bool {
                //     ...
                // }
                // glinear var g_return := g_expr;
                // atomic_finish(atomic_value, new_value, g_return);

                var atomicValueName = atomicStmt.atomicVar;
                var returnValueName = atomicStmt.ReturnId.val;

                bool isNoop = IsAtomicNoop(applySuffix.Lhs);

                string oldValueName, newValueName;
                if (isNoop)
                {
                    oldValueName = freshTempVarName("useless_old_value", codeContext);
                    newValueName = freshTempVarName("useless_new_value", codeContext);
                }
                else
                {
                    oldValueName = "old_value";
                    newValueName = "new_value";
                }

                var gName = acquireStmtVarName == null ? freshTempVarName("g", codeContext) : acquireStmtVarName;
                //var dummyBoolName = freshTempVarName("dummy_bool", codeContext);
                var gReturnName = freshTempVarName("g_return", codeContext);

                Statement returnValueDecl = null;
                if (atomicStmt.hasVar)
                {
                    returnValueDecl = IsReturnValueGhost(applySuffix.Lhs)
                        ? ghost_var_decl_empty(atomicStmt.Tok, returnValueName)
                        : var_decl_empty(atomicStmt.Tok, returnValueName);
                }

                List<Statement> newStmts = new List<Statement>
                {
                    isNoop
                        ? gshared_var_decl(atomicStmt.Tok, atomicValueName, atomicExpr)
                        : shared_var_decl(atomicStmt.Tok, atomicValueName, atomicExpr),
                    ghost_var_decl_empty(atomicStmt.Tok, oldValueName),
                    ghost_var_decl_empty(atomicStmt.Tok, newValueName),
                    glinear_var_decl_empty(atomicStmt.Tok, gName),
                    //ghost_var_decl(atomicStmt.Tok, dummyBoolName, new LiteralExpr(atomicStmt.Tok, true))
                };
                
                foreach (var previousAtomicVar in atomicVarStack)
                {
                    var asStmt = new AssertStmt(atomicStmt.Tok, atomicStmt.EndTok,
                        new BinaryExpr(atomicStmt.Tok,
                            BinaryExpr.Opcode.Neq,
                            namespace_call(atomicStmt.Tok, previousAtomicVar),
                            namespace_call(atomicStmt.Tok, atomicStmt.atomicVar)
                        ), null, null, null);
                    asStmt.AddCustomizedErrorMessage(
                        "Cannot show that the atomic cell is distinct from other currently-open atomics.");
                    newStmts.Add(asStmt);
                }
                
                List<Expression> lhss = new List<Expression>();
                List<AssignmentRhs> rhss = new List<AssignmentRhs>();
                lhss.Add(new IdentifierExpr(atomicStmt.Tok, returnValueName));
                lhss.Add(new IdentifierExpr(atomicStmt.Tok, oldValueName));
                lhss.Add(new IdentifierExpr(atomicStmt.Tok, newValueName));
                lhss.Add(new IdentifierExpr(atomicStmt.Tok, gName));
                var updatedArgList = applySuffix.Args.ToList();
                ApplySuffixArg asa = new ApplySuffixArg {
                    Inout = false, Expr = new NameSegment(atomicStmt.Tok, atomicValueName, null)
                };
                updatedArgList[0] = asa;
                var updatedCallExpr = new ApplySuffix(applySuffix.tok, applySuffix.AtTok, applySuffix.Lhs, updatedArgList);
                rhss.Add(new ExprRhs(updatedCallExpr));
                newStmts.Add(new UpdateStmt(atomicStmt.Tok, atomicStmt.Call.tok, lhss, rhss));

                var innerStmts = get_inner_stmts(atomicStmt);
                /*newStmts.Add(new IfStmt(
                    atomicStmt.Tok,
                    atomicStmt.EndTok,
                    false,
                    new IdentifierExpr(atomicStmt.Tok, dummyBoolName),
                    new BlockStmt(atomicStmt.Tok, atomicStmt.EndTok, innerStmts), null));*/
                newStmts.AddRange(innerStmts);

                var finalTok = releaseStmt == null ? atomicStmt.EndTok : releaseStmt.Tok;
                newStmts.Add(glinear_var_decl(finalTok, gReturnName, releaseStmtExpr == null ?
                    new IdentifierExpr(finalTok, gName) : releaseStmtExpr));
                
                // atomic_finish(atomic_value, new_value, g_return);
                var finishAtomicExpr = GetFinishAtomicExpr(applySuffix.Lhs);
                newStmts.Add(new UpdateStmt(
                    finalTok,
                    finalTok,
                    new List<Expression>(),
                    new List<AssignmentRhs>()
                    {
                        new ExprRhs(new ApplySuffix(finalTok, null, finishAtomicExpr, new List<ApplySuffixArg>()
                        {
                            new ApplySuffixArg { Inout = false, Expr = new NameSegment(finalTok, atomicValueName, null) },
                            new ApplySuffixArg { Inout = false, Expr = new NameSegment(finalTok, newValueName, null) },
                            new ApplySuffixArg { Inout = false, Expr = new NameSegment(finalTok, gReturnName, null) }
                        }))
                    }));

                if (atomicVarStack.Count == 0)
                {
                    var bs = new BlockStmt(atomicStmt.Tok, atomicStmt.EndTok, newStmts);
                    return returnValueDecl == null ? new List<Statement>() {bs}
                        : new List<Statement>() {returnValueDecl, bs};
                }
                else
                {
                    if (returnValueDecl != null)
                    {
                        newStmts.Insert(0, returnValueDecl);
                    }
                    return newStmts;
                }
            }

            private void TranslateStatementList(List<Statement> stmts)
            {
                for (int i = 0; i < stmts.Count; i++)
                {
                    if (stmts[i] is AtomicStmt atomicStmt)
                    {
                        List<Statement> newStmtList = GetNewStmtList(atomicStmt);
                        stmts.RemoveAt(i);
                        stmts.InsertRange(i, newStmtList);
                        i = i + newStmtList.Count - 1;
                    }
                }
            }

            public void VisitStatementList(List<Statement> stmts, bool isAtomicBlock = false)
            {
                
                for (int i = 0; i < stmts.Count; i++)
                {
                    if (isAtomicBlock && i == 0 && stmts[i] is AcquireStmt) continue;
                    if (isAtomicBlock && i == stmts.Count - 1 && stmts[i] is ReleaseStmt) continue;
                    VisitStatement(stmts[i]);

                    if (atomicVarStack != null && atomicVarStack.Count > 0)
                    {
                        Statement stmt = TryGhostifyStatement(stmts[i]);
                        if (stmt != null)
                        {
                            stmts[i] = stmt;
                        }
                    }
                }

                TranslateStatementList(stmts);
            }

            private void VisitStatement(Statement stmt)
            {
                switch (stmt)
                {
                    case BlockStmt bs:
                        VisitStatementList(bs.Body);
                        break;
                    case IfStmt ifs:
                        VisitStatementList(ifs.Thn.Body);
                        if (ifs.Els != null)
                        {
                            VisitStatement(ifs.Els);
                        }

                        break;
                    case NestedMatchStmt ms:
                        foreach (var mc in ms.Cases)
                        {
                            VisitStatementList(mc.Body);
                        }

                        break;
                    case WhileStmt ws:
                        if (ws.Body != null)
                        {
                            VisitStatementList(ws.Body.Body);
                        }

                        break;
                    
                    case AtomicStmt atomicStmt:
                        if (atomicVarStack == null)
                        {
                            atomicVarStack = new List<string>();
                        }

                        var atomicVar = freshTempVarName("atomic_tmp", codeContext);
                        atomicVarStack.Add(atomicVar);
                        atomicStmt.atomicVar = atomicVar;
                        
                        var body = atomicStmt.Body.Body;
                        VisitStatementList(atomicStmt.Body.Body, true);
                        
                        atomicVarStack.RemoveAt(atomicVarStack.Count - 1);
                        
                        break;
                    case ReleaseStmt releaseStmt:
                        reporter.Error(MessageSource.Rewriter, releaseStmt.Tok,
                        "A 'release' statement must be the last statement in an 'atomic' block");
                        break;
                    case AcquireStmt acquireStmt:
                        reporter.Error(MessageSource.Rewriter, acquireStmt.Tok,
                            "An 'acquire' statement must be first statement in an 'atomic' block");
                        break;
                }
            }

            private Statement TryGhostifyStatement(Statement stmt)
            {
                switch (stmt)
                {
                    case VarDeclStmt vds:
                        foreach (var local in vds.Locals)
                        {
                            if (local.Usage.IsOrdinaryKind)
                            {
                                local.Usage = Usage.Ghost;
                            }
                        }
                        break;
                    case IfStmt ifstmt:
                        ifstmt.forceGhost = true;
                        break;
                }

                return null;
            }

            private readonly ErrorReporter reporter;

            readonly FreshTempVarName freshTempVarName;
            private readonly ICodeContext codeContext;

            public AtomicBlockTranslator(ErrorReporter reporter, FreshTempVarName freshTempVarName, ICodeContext context)
            {
                this.reporter = reporter;
                this.freshTempVarName = freshTempVarName;
                this.codeContext = context;
            }
        }
        
        public delegate string FreshTempVarName(string prefix, ICodeContext context);
        FreshTempVarName freshTempVarName;

        public AtomicRewriter(ErrorReporter reporter, FreshTempVarName freshTempVarName) : base(reporter)
        {
            this.freshTempVarName = freshTempVarName;
        }
    }
}
