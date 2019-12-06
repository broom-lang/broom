* FType is parameterized over type variable type on type and fun level
* FTerm is a functor over concrete FType modules
* FlexFAst.Type is FType fixpoint-specialized to uv, ov and path
* FlexFAst.Term is FTerm(FlexFAst.Type)
* FixedFAst.Type is FType fixpoint-specialized to just names
* FixedFAst.Term is FTerm(FixedFAst.Type)
* TypeVars are parameterized over concrete FType.typ:s
* TypecheckingEnv will be renamed to TypingCtx
* FlexEnvironmentals contains operations on FlexFAst.Type that need TypingCtx
* FEnv will be F_c type environment, formerly FAstTypechecker.Env
* FixedEnvironmentals contains operations of FixedFAst.Type that need FEnv

