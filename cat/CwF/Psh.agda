{-OPTIONS -vtc.pos.tick:100 -vtc.pos.graph:100 -vtc.pos.check:100
              -vtc.pos.record:100 -vtc.pos.args:100 -vtc.pos:25-} 

open import willow.cat.CwF

module willow.cat.CwF.Psh {ℓoW ℓhW : Level} (ℓty ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open import willow.cat.Presheaf ℓty cW

postulate hole : ∀{ℓ} {A : Set ℓ} → A

cwfPsh : CwF (ℓoW ⊔ ℓhW ⊔ lsuc ℓty) (ℓoW ⊔ ℓhW ⊔ lsuc ℓty) ℓty ℓtm
CwF.cCtx cwfPsh = cPsh
CwF.∙ cwfPsh = p⊤
CwF.∙isterminal cwfPsh = hole --isterminal-p⊤
CwF.c-ty cwfPsh = hole
CwF.c-tm cwfPsh = hole
CwF.c-compr cwfPsh = hole
CwF.nt-wkn cwfPsh = hole
CwF.lim-var cwfPsh = hole
CwF.canpair cwfPsh = hole

--1 full CPU, but little memory consumption

{-

Statistics for willow.cat.CwF.Psh
A.Name  (fresh)                                                 383
A.Name (reused)                                               1,396
A.QName  (fresh)                                                278
A.QName (reused)                                              3,143
ByteString  (fresh)                                               0
ByteString (reused)                                               0
Double  (fresh)                                                   0
Double (reused)                                                   0
Integer  (fresh)                                                196
Integer (reused)                                                782
Node  (fresh)                                                 7,494
Node (reused)                                                88,968
Shared Term  (fresh)                                              0
Shared Term (reused)                                              0
String  (fresh)                                                 305
String (reused)                                               6,039
attempted-constraints                                             1
equal terms                                                 957,575
icode ()                                                         19
icode (Int,[Char])                                               60
icode (ModuleName,Scope)                                         30
icode (ModuleName,Section)                                        2
icode (ModuleName,Word64)                                         2
icode (Name,LocalVar)                                             5
icode (Name,[AbstractModule])                                    51
icode (Name,[AbstractName])                                     499
icode (NameSpaceId,NameSpace)                                   120
icode (QName,(WithArity CompiledClauses))                         9
icode (QName,Definition)                                          5
icode (QName,ModuleName)                                          1
icode (Range,Aspects)                                           104
icode (TopLevelModuleName,Int)                                   63
icode Abs (ClauseBodyF Term)                                     60
icode Abs (Tele (Dom (Type' Term)))                              70
icode Abs (Type' Term)                                           30
icode Abs Term                                                   13
icode AbsolutePath                                           11,972
icode AbstractModule                                             51
icode AbstractName                                              499
icode Arg (Named (Ranged [Char]) (Pattern' (Int,[Char])))        69
icode Arg (Named (Ranged [Char]) Int)                             6
icode Arg (Type' Term)                                           12
icode Arg Int                                                     1
icode Arg Term                                                5,694
icode Arg [Char]                                                 60
icode ArgInfo                                                 5,960
icode Aspect                                                    104
icode Aspects                                                   104
icode Associativity                                             383
icode Bool                                                      131
icode Case CompiledClauses                                        1
icode Clause                                                     12
icode ClauseBodyF Term                                           72
icode CompiledClauses                                            13
icode CompiledRepresentation                                      5
icode CompressedFile                                              1
icode ConHead                                                    10
icode Definition                                                  5
icode Defn                                                        5
icode Delayed                                                     4
icode Dom (Type' Term)                                          100
icode Elim' Term                                              5,876
icode Fixity                                                    383
icode Fixity'                                                   383
icode FunctionInverse' Clause                                     4
icode GenPart                                                    21
icode HashMap QName Definition                                    1
icode HashMap QName [RewriteRule]                                 1
icode Hiding                                                  5,960
icode Induction                                                  10
icode Int                                                     3,673
icode Int32                                                  35,927
icode Integer                                                   978
icode Interface                                                   1
icode Interval' (Maybe AbsolutePath)                          5,986
icode IsAbstract                                                  4
icode KindOfName                                                499
icode Level                                                     155
icode LevelAtom                                                 185
icode LocalVar                                                    5
icode Map Literal CompiledClauses                                 1
icode Map ModuleName Scope                                        2
icode Map ModuleName Section                                      1
icode Map Name [AbstractModule]                                 120
icode Map Name [AbstractName]                                   120
icode Map QName (WithArity CompiledClauses)                       1
icode Map QName ([Arg Name],(Pattern' Void))                      1
icode Map QName ModuleName                                       30
icode Map [Char] (Builtin ([Char],QName))                         1
icode Maybe (Arg (Type' Term))                                   12
icode Maybe (Ranged [Char])                                      75
icode Maybe (TopLevelModuleName,Int)                            104
icode Maybe AbsolutePath                                     23,944
icode Maybe Aspect                                              104
icode Maybe Bool                                                  4
icode Maybe CompiledClauses                                       5
icode Maybe CoreRepresentation                                    5
icode Maybe Exp                                                   5
icode Maybe ExtLamInfo                                            4
icode Maybe HaskellExport                                         5
icode Maybe HaskellRepresentation                                 5
icode Maybe NameKind                                             63
icode Maybe Projection                                            4
icode Maybe QName                                                 9
icode Maybe [Char]                                              109
icode ModuleName                                                451
icode MutualId                                                    5
icode Name                                                    7,388
icode NameId                                                    384
icode NameKind                                                   63
icode NamePart                                                5,959
icode NameSpace                                                 120
icode NameSpaceId                                               120
icode Named (Ranged [Char]) (Pattern' (Int,[Char]))              69
icode Named (Ranged [Char]) Int                                   6
icode Occurrence                                                 16
icode Pattern' (Int,[Char])                                      69
icode PlusLevel                                                 185
icode Polarity                                                   16
icode Position' (Maybe AbsolutePath)                         11,972
icode Precedence                                                  1
icode PrecedenceLevel                                           383
icode QName                                                   8,092
icode Range                                                     104
icode Range' (Maybe AbsolutePath)                             6,447
icode Ranged [Char]                                              60
icode Relevance                                               5,960
icode Scope                                                      30
icode ScopeInfo                                                   1
icode Section                                                     2
icode Set [Char]                                                  2
icode Signature                                                   1
icode Sort                                                      148
icode Tele (Dom (Type' Term))                                    84
icode Term                                                    6,063
icode TopLevelModuleName                                         63
icode Type' Term                                                147
icode WhyInScope                                              2,126
icode WithArity CompiledClauses                                   9
icode Word64                                                      3
icode [(Literal,CompiledClauses)]                                 1
icode [(ModuleName,Scope)]                                        2
icode [(ModuleName,Section)]                                      1
icode [(ModuleName,Word64)]                                       1
icode [(Name,LocalVar)]                                           1
icode [(Name,[AbstractModule])]                                 120
icode [(Name,[AbstractName])]                                   120
icode [(NameSpaceId,NameSpace)]                                  30
icode [(QName,(WithArity CompiledClauses))]                       1
icode [(QName,([Arg Name],(Pattern' Void)))]                      1
icode [(QName,Definition)]                                        1
icode [(QName,ModuleName)]                                       30
icode [(QName,[RewriteRule])]                                     1
icode [(Range,Aspects)]                                           1
icode [([Char],(Builtin ([Char],QName)))]                         1
icode [AbstractModule]                                           51
icode [AbstractName]                                            499
icode [Arg (Named (Ranged [Char]) (Pattern' (Int,[Char])))]      12
icode [Arg Term]                                                 10
icode [Arg [Char]]                                               12
icode [Char]                                                  6,344
icode [Clause]                                                    4
icode [Elim' Term]                                            2,664
icode [GenPart]                                                 383
icode [Interval' (Maybe AbsolutePath)]                        6,447
icode [ModuleName]                                               30
icode [NamePart]                                              5,608
icode [Name]                                                    451
icode [Occurrence]                                                5
icode [Open DisplayForm]                                          5
icode [OtherAspect]                                             104
icode [PlusLevel]                                               155
icode [Polarity]                                                  5
icode [QName]                                                    14
icode [[Char]]                                                  100
icode [[[Char]]]                                                  1
max-open-constraints                                              1
max-open-metas                                                    2
metas                                                            21
pointers  (fresh)                                                 0
pointers (reused)                                                 0
unequal terms                                               280,104

Finished willow.cat.CwF.Psh.
Total                      284,712ms
Miscellaneous                    7ms
Parsing                          1ms
Parsing.Operators                5ms
Import                          10ms
Deserialization                622ms
Scoping                          1ms
Typing                           4ms
Typing.OccursCheck               2ms
Typing.CheckLHS            283,718ms
Termination                      4ms
Termination.Graph                0ms
Termination.RecCheck             0ms
Termination.Compare              3ms
Positivity                       8ms
Injectivity                      0ms
ProjectionLikeness               0ms
Coverage                         0ms
Highlighting                     2ms
Serialization                  285ms
Serialization.Sort               1ms
Serialization.BinaryEncode      11ms
Serialization.Compress           1ms
DeadCode                         2ms
ModuleName                      15ms

Accumlated statistics
A.Name  (fresh)                                                 383
A.Name (reused)                                               1,396
A.QName  (fresh)                                                278
A.QName (reused)                                              3,143
ByteString  (fresh)                                               0
ByteString (reused)                                               0
Double  (fresh)                                                   0
Double (reused)                                                   0
Integer  (fresh)                                                196
Integer (reused)                                                782
Node  (fresh)                                                 7,494
Node (reused)                                                88,968
Shared Term  (fresh)                                              0
Shared Term (reused)                                              0
String  (fresh)                                                 305
String (reused)                                               6,039
attempted-constraints                                             1
equal terms                                                 957,575
icode ()                                                         19
icode (Int,[Char])                                               60
icode (ModuleName,Scope)                                         30
icode (ModuleName,Section)                                        2
icode (ModuleName,Word64)                                         2
icode (Name,LocalVar)                                             5
icode (Name,[AbstractModule])                                    51
icode (Name,[AbstractName])                                     499
icode (NameSpaceId,NameSpace)                                   120
icode (QName,(WithArity CompiledClauses))                         9
icode (QName,Definition)                                          5
icode (QName,ModuleName)                                          1
icode (Range,Aspects)                                           104
icode (TopLevelModuleName,Int)                                   63
icode Abs (ClauseBodyF Term)                                     60
icode Abs (Tele (Dom (Type' Term)))                              70
icode Abs (Type' Term)                                           30
icode Abs Term                                                   13
icode AbsolutePath                                           11,972
icode AbstractModule                                             51
icode AbstractName                                              499
icode Arg (Named (Ranged [Char]) (Pattern' (Int,[Char])))        69
icode Arg (Named (Ranged [Char]) Int)                             6
icode Arg (Type' Term)                                           12
icode Arg Int                                                     1
icode Arg Term                                                5,694
icode Arg [Char]                                                 60
icode ArgInfo                                                 5,960
icode Aspect                                                    104
icode Aspects                                                   104
icode Associativity                                             383
icode Bool                                                      131
icode Case CompiledClauses                                        1
icode Clause                                                     12
icode ClauseBodyF Term                                           72
icode CompiledClauses                                            13
icode CompiledRepresentation                                      5
icode CompressedFile                                              1
icode ConHead                                                    10
icode Definition                                                  5
icode Defn                                                        5
icode Delayed                                                     4
icode Dom (Type' Term)                                          100
icode Elim' Term                                              5,876
icode Fixity                                                    383
icode Fixity'                                                   383
icode FunctionInverse' Clause                                     4
icode GenPart                                                    21
icode HashMap QName Definition                                    1
icode HashMap QName [RewriteRule]                                 1
icode Hiding                                                  5,960
icode Induction                                                  10
icode Int                                                     3,673
icode Int32                                                  35,927
icode Integer                                                   978
icode Interface                                                   1
icode Interval' (Maybe AbsolutePath)                          5,986
icode IsAbstract                                                  4
icode KindOfName                                                499
icode Level                                                     155
icode LevelAtom                                                 185
icode LocalVar                                                    5
icode Map Literal CompiledClauses                                 1
icode Map ModuleName Scope                                        2
icode Map ModuleName Section                                      1
icode Map Name [AbstractModule]                                 120
icode Map Name [AbstractName]                                   120
icode Map QName (WithArity CompiledClauses)                       1
icode Map QName ([Arg Name],(Pattern' Void))                      1
icode Map QName ModuleName                                       30
icode Map [Char] (Builtin ([Char],QName))                         1
icode Maybe (Arg (Type' Term))                                   12
icode Maybe (Ranged [Char])                                      75
icode Maybe (TopLevelModuleName,Int)                            104
icode Maybe AbsolutePath                                     23,944
icode Maybe Aspect                                              104
icode Maybe Bool                                                  4
icode Maybe CompiledClauses                                       5
icode Maybe CoreRepresentation                                    5
icode Maybe Exp                                                   5
icode Maybe ExtLamInfo                                            4
icode Maybe HaskellExport                                         5
icode Maybe HaskellRepresentation                                 5
icode Maybe NameKind                                             63
icode Maybe Projection                                            4
icode Maybe QName                                                 9
icode Maybe [Char]                                              109
icode ModuleName                                                451
icode MutualId                                                    5
icode Name                                                    7,388
icode NameId                                                    384
icode NameKind                                                   63
icode NamePart                                                5,959
icode NameSpace                                                 120
icode NameSpaceId                                               120
icode Named (Ranged [Char]) (Pattern' (Int,[Char]))              69
icode Named (Ranged [Char]) Int                                   6
icode Occurrence                                                 16
icode Pattern' (Int,[Char])                                      69
icode PlusLevel                                                 185
icode Polarity                                                   16
icode Position' (Maybe AbsolutePath)                         11,972
icode Precedence                                                  1
icode PrecedenceLevel                                           383
icode QName                                                   8,092
icode Range                                                     104
icode Range' (Maybe AbsolutePath)                             6,447
icode Ranged [Char]                                              60
icode Relevance                                               5,960
icode Scope                                                      30
icode ScopeInfo                                                   1
icode Section                                                     2
icode Set [Char]                                                  2
icode Signature                                                   1
icode Sort                                                      148
icode Tele (Dom (Type' Term))                                    84
icode Term                                                    6,063
icode TopLevelModuleName                                         63
icode Type' Term                                                147
icode WhyInScope                                              2,126
icode WithArity CompiledClauses                                   9
icode Word64                                                      3
icode [(Literal,CompiledClauses)]                                 1
icode [(ModuleName,Scope)]                                        2
icode [(ModuleName,Section)]                                      1
icode [(ModuleName,Word64)]                                       1
icode [(Name,LocalVar)]                                           1
icode [(Name,[AbstractModule])]                                 120
icode [(Name,[AbstractName])]                                   120
icode [(NameSpaceId,NameSpace)]                                  30
icode [(QName,(WithArity CompiledClauses))]                       1
icode [(QName,([Arg Name],(Pattern' Void)))]                      1
icode [(QName,Definition)]                                        1
icode [(QName,ModuleName)]                                       30
icode [(QName,[RewriteRule])]                                     1
icode [(Range,Aspects)]                                           1
icode [([Char],(Builtin ([Char],QName)))]                         1
icode [AbstractModule]                                           51
icode [AbstractName]                                            499
icode [Arg (Named (Ranged [Char]) (Pattern' (Int,[Char])))]      12
icode [Arg Term]                                                 10
icode [Arg [Char]]                                               12
icode [Char]                                                  6,344
icode [Clause]                                                    4
icode [Elim' Term]                                            2,664
icode [GenPart]                                                 383
icode [Interval' (Maybe AbsolutePath)]                        6,447
icode [ModuleName]                                               30
icode [NamePart]                                              5,608
icode [Name]                                                    451
icode [Occurrence]                                                5
icode [Open DisplayForm]                                          5
icode [OtherAspect]                                             104
icode [PlusLevel]                                               155
icode [Polarity]                                                  5
icode [QName]                                                    14
icode [[Char]]                                                  100
icode [[[Char]]]                                                  1
max-open-constraints                                              1
max-open-metas                                                    2
metas                                                            21
pointers  (fresh)                                                 0
pointers (reused)                                                 0
unequal terms                                               280,104


-}
