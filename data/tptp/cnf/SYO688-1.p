%------------------------------------------------------------------------------
% File     : SYO688-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_2_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_2_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.29 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     : 1167 (   2 unt; 839 nHn;1166 RR)
%            Number of literals    : 12472 (   0 equ;10008 neg)
%            Maximal clause size   :   14 (  10 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   : 3160 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_311,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_61,axiom,
    ( ~ 'E'('0',f(suc(suc(B_92))))
    | ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'(f(B_92),f(suc(B_92)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'('0',f(B_92))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_975,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(B_94)) ) ).

cnf(clause_233,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(B_92))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(B_91),f(suc(B_91)))
    | 'E'(f(B_92),f(suc(B_92))) ) ).

cnf(clause_944,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_25))),s(s('0')))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(suc(suc(C_25))))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_1120,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_6))),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(suc(suc(C_6))))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_550,axiom,
    ( ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_668,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(B_39),suc(B_39)) ) ).

cnf(clause_260,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_365,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(C_30))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(suc(suc(C_30))))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_101,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_77),f(suc(B_77))) ) ).

cnf(clause_556,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_0)),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(suc(C_0)))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_289,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(C_32),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(C_32))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_99,axiom,
    ( ~ 'E'(f(B_1),f(suc(B_1)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_1))))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_879,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_22),f(suc(B_22))) ) ).

cnf(clause_46,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_5))),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(suc(suc(C_5))))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_815,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_23),f(suc(B_23))) ) ).

cnf(clause_677,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_40,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_49))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(suc(B_49))))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_97,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_214,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'LE'(f(suc(suc(C_12))),s('0'))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(C_12))))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_314,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_58),f(suc(B_58))) ) ).

cnf(clause_206,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(suc(C_22)),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(C_22)))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_686,axiom,
    ( ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_703,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(C_4),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(C_4))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_398,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(suc(suc(C_23))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(suc(suc(C_23))))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_950,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(f(B_34),f(suc(B_34)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_34))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_763,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_1000,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ 'E'(f(B_40),f(suc(B_40)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_40))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_391,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_15),f(suc(B_15))) ) ).

cnf(clause_493,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_34),f(suc(B_34))) ) ).

cnf(clause_574,axiom,
    ( ~ 'E'(f(B_0),f(suc(B_0)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B_0))))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0)) ) ).

cnf(clause_1059,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(B_38),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s(s('0'))),f(B_38))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_869,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72))) ) ).

cnf(clause_73,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_22),f(suc(B_22))) ) ).

cnf(clause_1095,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_35),f(suc(B_35))) ) ).

cnf(clause_91,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_523,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_985,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(f(B_76),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(B_76))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_79,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_5),s(s(s('0'))))
    | 'E'(s(s('0')),f(C_5))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_1081,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(B_72),suc(B_72)) ) ).

cnf(clause_322,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'('0',f(suc(suc(B_78))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_78),f(suc(B_78)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_942,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_5),s(s(s('0'))))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(C_5))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_52,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_9),f(suc(B_9)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_9))))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_1088,axiom,
    ( ~ 'LE'(f(suc(suc(B_90))),s('0'))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'('0',f(suc(suc(B_90))))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_710,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | iLEQ(suc(B_91),suc(B_91)) ) ).

cnf(clause_669,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(C_32),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(C_32))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_158,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B),suc(B)) ) ).

cnf(clause_645,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(B_79))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(suc(suc(B_79))))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_1129,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_41),f(suc(B_41))) ) ).

cnf(clause_416,axiom,
    ( ~ 'LE'(f(suc(C_30)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(suc(C_30)))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_657,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_85),f(suc(B_85))) ) ).

cnf(clause_300,axiom,
    ( ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s('0'),f(suc(suc(B_4))))
    | ~ iLEQ(suc(B),suc(B_4)) ) ).

cnf(clause_577,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(B_94),f(suc(B_94))) ) ).

cnf(clause_315,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_1),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(C_1))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_344,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_0),f(suc(B_0))) ) ).

cnf(clause_834,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_50),f(suc(B_50)))
    | iLEQ(suc(B_50),suc(B_50)) ) ).

cnf(clause_286,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'('0',f(suc(suc(B_66))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_66),f(suc(B_66)))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_431,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(B_13),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_13))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_695,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ 'LE'(f(suc(C_23)),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(C_23)))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_863,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(C_30),s(s('0')))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(C_30))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_433,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'LE'(f(suc(C_17)),s('0'))
    | 'E'('0',f(suc(C_17)))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_736,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_1138,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_91),f(suc(B_91))) ) ).

cnf(clause_744,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_330,axiom,
    ( ~ 'LE'(f(suc(C)),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(s(s(s(s('0')))),f(suc(C)))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_1125,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_448,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(C_32),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(C_32))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_287,axiom,
    ( ~ 'E'('0',f(suc(suc(B_48))))
    | ~ 'E'(f(B_48),f(suc(B_48)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_510,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | iLEQ(suc(B_14),suc(B_14)) ) ).

cnf(clause_993,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(C_32))),s('0'))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(suc(suc(C_32))))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_697,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_26))),s('0'))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'('0',f(suc(suc(C_26))))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_153,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(f(B_27),f(suc(B_27)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'('0',f(suc(suc(B_27))))
    | ~ 'E'('0',f(B_27)) ) ).

cnf(clause_1112,axiom,
    ( ~ 'LE'(f(suc(suc(C_33))),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(suc(suc(C_33))))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_1098,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_6))),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(C_6))))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_1147,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_16))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(suc(C_16))))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_489,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(B_27),f(suc(B_27))) ) ).

cnf(clause_230,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_28),s('0'))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'('0',f(C_28))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_271,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(C_18),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(C_18))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_401,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_24),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(C_24))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_811,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'LE'(f(suc(suc(C_18))),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(suc(suc(C_18))))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_1130,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_35),f(suc(B_35))) ) ).

cnf(clause_801,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_13))),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(suc(B_13))))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_541,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_9),f(suc(B_9)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_9))))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9)) ) ).

cnf(clause_628,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(B_49),s(s('0')))
    | 'E'(s('0'),f(B_49))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_421,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_15))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(f(B_15),f(suc(B_15)))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_774,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'LE'(f(suc(C_8)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(C_8)))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_253,axiom,
    ( ~ 'LE'(f(suc(suc(C_19))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(suc(suc(C_19))))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_919,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_107,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_348,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_24),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s(s('0')),f(C_24))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_299,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_10,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(B_71),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(B_71))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_144,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(C_20))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(suc(suc(C_20))))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_862,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(suc(C_7)),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(suc(C_7)))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_761,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'LE'(f(suc(C_13)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(C_13)))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_892,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_84),f(suc(B_84))) ) ).

cnf(clause_684,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_13),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(C_13))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_498,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'LE'(f(suc(C_13)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(C_13)))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_795,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_15),f(suc(B_15))) ) ).

cnf(clause_589,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_277,axiom,
    ( ~ 'LE'(f(C_18),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(C_18))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_494,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_9),f(suc(B_9)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_9))))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_720,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_44))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(suc(suc(B_44))))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_633,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_5))),s(s(s('0'))))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(suc(suc(C_5))))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_875,axiom,
    ( ~ 'E'(f(B_1),f(suc(B_1)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_1))))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_730,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_457,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(suc(C_7)),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_7)))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_218,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_664,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_59),f(suc(B_59))) ) ).

cnf(clause_719,axiom,
    ( ~ 'LE'(f(suc(B_28)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(B_28)))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_987,axiom,
    ( ~ 'LE'(f(suc(suc(C_14))),s(s(s(s('0')))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_14))))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_425,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(B_79),s(s('0')))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(B_79))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_102,axiom,
    ( ~ 'LE'(f(suc(suc(C))),s(s(s(s(s('0'))))))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(suc(suc(C))))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_458,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(f(B_34),f(suc(B_34)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_34))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32)) ) ).

cnf(clause_268,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_22),s('0'))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(C_22))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_320,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(C_20))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(suc(C_20))))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_949,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(C_15),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s('0')),f(C_15))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_67,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | iLEQ(suc(B_57),suc(B_57)) ) ).

cnf(clause_427,axiom,
    ( ~ 'LE'(f(suc(C_16)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(suc(C_16)))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_849,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_40),f(suc(B_40))) ) ).

cnf(clause_235,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(suc(C_0))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(s(s(s('0'))),f(suc(suc(C_0))))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_547,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(B_44)),s(s(s('0'))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(B_44)))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_1134,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_1))),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(suc(C_1))))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_743,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(suc(B_95))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(B_95),f(suc(B_95)))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95)) ) ).

cnf(clause_898,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(B_45),suc(B_45)) ) ).

cnf(clause_468,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_756,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_51),f(suc(B_51))) ) ).

cnf(clause_64,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_76),f(suc(B_76))) ) ).

cnf(clause_551,axiom,
    ( ~ 'E'('0',f(suc(suc(B_48))))
    | ~ 'E'(f(B_48),f(suc(B_48)))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1080,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_59),f(suc(B_59))) ) ).

cnf(clause_437,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_35))))
    | ~ 'E'(f(B_35),f(suc(B_35)))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_783,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(B_59),f(suc(B_59))) ) ).

cnf(clause_685,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_9),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(C_9))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_773,axiom,
    ( ~ 'LE'(f(suc(B_74)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_74)))
    | 'LE'(f(B_74),s(s('0'))) ) ).

cnf(clause_179,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(B_29),f(suc(B_29)))
    | iLEQ(suc(B_29),suc(B_29)) ) ).

cnf(clause_236,axiom,
    ( ~ 'LE'(f(suc(suc(C_27))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(suc(suc(C_27))))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_406,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_1123,axiom,
    ( ~ 'LE'(f(suc(suc(B_56))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_56))))
    | 'LE'(f(B_56),s(s(s('0')))) ) ).

cnf(clause_389,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_9)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s('0'),f(suc(C_9)))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_27,axiom,
    ( ~ 'LE'(f(suc(C_19)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(C_19)))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_189,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_59))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(f(B_59),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_522,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_40),f(suc(B_40))) ) ).

cnf(clause_1007,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_2))),s(s('0')))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(suc(suc(C_2))))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_904,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_33),f(suc(B_33))) ) ).

cnf(clause_403,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_26))),s('0'))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(suc(C_26))))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_572,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'LE'(f(C_29),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(C_29))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_171,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_800,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'LE'(f(suc(suc(C_28))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(suc(C_28))))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_1053,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_757,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'LE'(f(suc(C_14)),s(s(s(s('0')))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s(s('0'))),f(suc(C_14)))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_877,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_77),f(suc(B_77))) ) ).

cnf(clause_1158,axiom,
    ( ~ 'LE'(f(B_86),s(s('0')))
    | 'E'(s('0'),f(B_86))
    | 'LE'(f(B_86),s('0')) ) ).

cnf(clause_529,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1069,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_620,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(suc(C_7)),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(suc(C_7)))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_583,axiom,
    ( ~ 'LE'(f(suc(B_79)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(suc(B_79)))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_652,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | iLEQ(suc(B_87),suc(B_87)) ) ).

cnf(clause_51,axiom,
    ( ~ 'LE'(f(C_33),s('0'))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(C_33))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_72,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'LE'(f(C_21),s(s('0')))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(C_21))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_1117,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'LE'(f(suc(suc(C_29))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(suc(suc(C_29))))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_412,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_35),f(suc(B_35))) ) ).

cnf(clause_961,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'LE'(f(suc(suc(C_0))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_0))))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_680,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_0)),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(C_0)))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_503,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_7),suc(B_7)) ) ).

cnf(clause_1135,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'LE'(f(suc(C_28)),s('0'))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'('0',f(suc(C_28)))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_164,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_771,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_47),f(suc(B_47)))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s('0'),f(suc(suc(B_47))))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_269,axiom,
    ( ~ 'LE'(f(suc(B_56)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_56)))
    | 'LE'(f(B_56),s(s(s('0')))) ) ).

cnf(clause_438,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'LE'(f(suc(B_90)),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'('0',f(suc(B_90)))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_643,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_12))),s('0'))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(suc(suc(C_12))))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_752,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'LE'(f(suc(C_8)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(C_8)))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_1102,axiom,
    ( ~ 'LE'(f(suc(suc(C_21))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(suc(suc(C_21))))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_120,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | iLEQ(suc(B_32),suc(B_32)) ) ).

cnf(clause_1038,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_1090,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(C_31),s('0'))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(C_31))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_1056,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_727,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s('0'),f(suc(suc(B_42))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1154,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'('0',f(suc(B_73)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_73),f(suc(B_73))) ) ).

cnf(clause_259,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(B_25),f(suc(B_25)))
    | iLEQ(suc(B_25),suc(B_25)) ) ).

cnf(clause_445,axiom,
    ( ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s('0'),f(suc(suc(B_4))))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_941,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_6)),s(s(s(s(s('0'))))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_640,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_19,axiom,
    ( ~ 'LE'(f(suc(C_8)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(C_8)))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_1029,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'LE'(f(suc(suc(C_23))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(suc(C_23))))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_479,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'LE'(f(suc(C_31)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(suc(C_31)))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_1122,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_579,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_47),f(suc(B_47)))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s('0'),f(suc(suc(B_47))))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1131,axiom,
    ( ~ 'LE'(f(suc(C_16)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(suc(C_16)))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_1023,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_888,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_150,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_9),f(suc(B_9))) ) ).

cnf(clause_742,axiom,
    ( ~ 'LE'(f(suc(C_30)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(suc(C_30)))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_366,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_110,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_49))),s(s('0')))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(suc(B_49))))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_983,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(B_11))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_638,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_47,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_66),f(suc(B_66))) ) ).

cnf(clause_994,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(B_19),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(B_19))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_738,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_6))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(C_6))))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_531,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(B_84),suc(B_84)) ) ).

cnf(clause_1063,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_612,axiom,
    ( ~ 'LE'(f(suc(suc(C_19))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(suc(suc(C_19))))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_1046,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'LE'(f(C_21),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(C_21))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_903,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(f(B_27),f(suc(B_27)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'('0',f(suc(suc(B_27))))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_58,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'LE'(f(suc(C_31)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(C_31)))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_802,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s('0'),f(suc(suc(B_17))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_114,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_58))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_58),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_232,axiom,
    ( ~ 'E'('0',f(suc(suc(B_55))))
    | ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54)))) ) ).

cnf(clause_519,axiom,
    ( ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(s('0'),f(suc(suc(B_4))))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_1145,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_60),f(suc(B_60))) ) ).

cnf(clause_1014,axiom,
    ( ~ 'E'(f(B_22),f(suc(B_22)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(s('0'),f(suc(suc(B_22))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_1074,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_33))))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(f(B_33),f(suc(B_33)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_252,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(B_52),f(suc(B_52))) ) ).

cnf(clause_788,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(C_4),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(C_4))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_117,axiom,
    ( ~ 'LE'(f(suc(suc(C_15))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(suc(suc(C_15))))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_902,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s('0'),f(suc(suc(B_17))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14))) ) ).

cnf(clause_542,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(B_94))
    | iLEQ(suc(B_94),suc(B_94)) ) ).

cnf(clause_354,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_324,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_7),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(C_7))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_381,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_240,axiom,
    ( ~ 'LE'(f(suc(C_10)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(suc(C_10)))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_393,axiom,
    ( ~ 'E'(f(B_1),f(suc(B_1)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_1))))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_274,axiom,
    ( ~ 'LE'(f(suc(C_19)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(C_19)))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_940,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(suc(suc(C_9))),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s('0'),f(suc(suc(C_9))))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_199,axiom,
    ( ~ 'LE'(f(B_93),s('0'))
    | 'E'('0',f(B_93))
    | 'LE'(f(B_93),'0') ) ).

cnf(clause_599,axiom,
    ( ~ 'LE'(f(suc(B_6)),s(s(s(s(s('0'))))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_173,axiom,
    ( ~ 'LE'(f(suc(suc(C_22))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(suc(suc(C_22))))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_964,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_24)),s(s(s('0'))))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s(s('0')),f(suc(C_24)))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_11,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_24))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(suc(suc(C_24))))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_852,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_28))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'('0',f(suc(suc(C_28))))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_662,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(B_45),suc(B_45)) ) ).

cnf(clause_1044,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_17))),s('0'))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'('0',f(suc(suc(C_17))))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_636,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_29),f(suc(B_29)))
    | iLEQ(suc(B_29),suc(B_29)) ) ).

cnf(clause_665,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_1132,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_27),f(suc(B_27))) ) ).

cnf(clause_982,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_2))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_316,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_7))),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(C_7))))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_453,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(C_23),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(C_23))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_770,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_46),f(suc(B_46))) ) ).

cnf(clause_217,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | iLEQ(suc(B_29),suc(B_29)) ) ).

cnf(clause_499,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(C_17),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(C_17))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_363,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_923,axiom,
    ( ~ 'LE'(f(suc(suc(C_10))),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(suc(suc(C_10))))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_450,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_24)),s(s(s('0'))))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(C_24)))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_176,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'('0',f(suc(suc(B_70))))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_492,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_60),f(suc(B_60))) ) ).

cnf(clause_826,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(f(B_88),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(B_88))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_1084,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | iLEQ(suc(B_63),suc(B_63)) ) ).

cnf(clause_1068,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_963,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_41))))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(f(B_41),f(suc(B_41)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_455,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(s('0'),f(suc(suc(B_81))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_642,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(suc(C_22)),s('0'))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(suc(C_22)))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_838,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_23),f(suc(B_23)))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_23))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_1004,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | iLEQ(suc(B_39),suc(B_39)) ) ).

cnf(clause_1096,axiom,
    ( ~ 'LE'(f(suc(suc(C_22))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(suc(suc(C_22))))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_329,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(B_83),s('0'))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(B_83))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_952,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_9)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(suc(C_9)))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_1061,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_370,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_441,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_11))),s(s('0')))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(s('0'),f(suc(suc(C_11))))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_806,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_26))),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(suc(suc(C_26))))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_939,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_196,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_3))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_138,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | iLEQ(suc(B_7),suc(B_7)) ) ).

cnf(clause_194,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'LE'(f(suc(C_18)),s(s(s('0'))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(C_18)))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_977,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_653,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_34),f(suc(B_34)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_34))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_1162,axiom,
    ( ~ 'LE'(f(suc(suc(C_21))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(suc(suc(C_21))))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_1048,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'LE'(f(C_6),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(C_6))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_376,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(B_51),f(suc(B_51))) ) ).

cnf(clause_466,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_9),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s('0'),f(C_9))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_593,axiom,
    ( ~ 'LE'(f(suc(suc(B_53))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(suc(B_53))))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_417,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_1161,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_54),f(suc(B_54)))
    | iLEQ(suc(B_54),suc(B_54)) ) ).

cnf(clause_917,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_595,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_481,axiom,
    ( ~ 'LE'(f(suc(C_12)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(suc(C_12)))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_237,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_487,axiom,
    ( ~ 'LE'(f(suc(C_19)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(suc(C_19)))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_390,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | iLEQ(suc(B_25),suc(B_25)) ) ).

cnf(clause_255,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s('0'),f(suc(suc(B_81))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_627,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_0),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(C_0))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_566,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_9),f(suc(B_9)))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_9))))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_598,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'LE'(f(C_10),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'('0',f(C_10))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_98,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'LE'(f(suc(suc(C_12))),s('0'))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'('0',f(suc(suc(C_12))))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_1148,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_13),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(C_13))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_837,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_161,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_11),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(C_11))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_212,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'LE'(f(suc(suc(C_13))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(suc(C_13))))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_1160,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_53))),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(suc(B_53))))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_130,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_831,axiom,
    ( ~ 'LE'(f(C_18),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(C_18))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_1103,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_16),f(suc(B_16))) ) ).

cnf(clause_1001,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_614,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_22),s('0'))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(C_22))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_554,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'('0',f(suc(suc(B_70))))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_682,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_116,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'LE'(f(suc(C_5)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(C_5)))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_454,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_889,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(f(B_27),f(suc(B_27)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'('0',f(suc(suc(B_27))))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_386,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(A_0),suc(A_0)) ) ).

cnf(clause_155,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(C_10)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(suc(C_10)))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_751,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(C_6),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(C_6))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_129,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'LE'(f(suc(C_25)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(C_25)))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_396,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(suc(C_33)),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(suc(C_33)))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_497,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'LE'(f(suc(suc(C_4))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_4))))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_910,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_95))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(B_95),f(suc(B_95)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(B_94),f(suc(B_94))) ) ).

cnf(clause_257,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_8))))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_371,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'LE'(f(suc(C_5)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(C_5)))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_504,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_784,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(B_36))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_755,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4)) ) ).

cnf(clause_732,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_1108,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_367,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(C_27)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(suc(C_27)))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_724,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'LE'(f(C_2),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(C_2))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_972,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_23),f(suc(B_23)))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_23))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_204,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'LE'(f(C_10),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(C_10))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_660,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_1055,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_84),f(suc(B_84)))
    | iLEQ(suc(B_84),suc(B_84)) ) ).

cnf(clause_792,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(C_5)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(suc(C_5)))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_764,axiom,
    ( ~ 'LE'(f(C_16),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(C_16))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_152,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_203,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_65),f(suc(B_65))) ) ).

cnf(clause_229,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(C_29)),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'('0',f(suc(C_29)))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_558,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(suc(suc(C_9))),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(C_9))))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_209,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'LE'(f(suc(C_25)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s('0'),f(suc(C_25)))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_825,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | iLEQ(suc(B_7),suc(B_7)) ) ).

cnf(clause_524,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_1042,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C_0),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(C_0))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_1101,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_59))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(f(B_59),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57)))) ) ).

cnf(clause_353,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ 'E'(f(B_40),f(suc(B_40)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_40))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_30,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(B_53)),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(B_53)))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_699,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_95))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(B_95),f(suc(B_95)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_94),f(suc(B_94))) ) ).

cnf(clause_1152,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_23),f(suc(B_23))) ) ).

cnf(clause_463,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_41))))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_41),f(suc(B_41)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_658,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_8),s(s(s('0'))))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(C_8))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_508,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_165,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_349,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_16),f(suc(B_16))) ) ).

cnf(clause_729,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(suc(suc(B_38))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_38))))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_456,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'LE'(f(suc(suc(C_29))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'('0',f(suc(suc(C_29))))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_215,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_42))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_536,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(suc(C_32)),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(C_32)))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_932,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_89),f(suc(B_89))) ) ).

cnf(clause_1151,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'(f(B_89),f(suc(B_89))) ) ).

cnf(clause_683,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'(f(B_51),f(suc(B_51))) ) ).

cnf(clause_647,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_857,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'LE'(f(C_29),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(C_29))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_409,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(B_50),suc(B_50)) ) ).

cnf(clause_82,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_585,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_25))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(suc(C_25))))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_740,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(B_33),f(suc(B_33))) ) ).

cnf(clause_790,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_886,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_26),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(C_26))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_325,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C_0),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(C_0))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_855,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_11),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(C_11))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_974,axiom,
    ( ~ 'LE'(f(suc(suc(C_31))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(suc(C_31))))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_340,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_90,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_318,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'LE'(f(suc(suc(C_8))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(suc(C_8))))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_434,axiom,
    ( ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_272,axiom,
    ( ~ 'LE'(f(suc(C_20)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(suc(C_20)))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_1010,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_13),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(C_13))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_546,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_711,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_41))))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_41),f(suc(B_41)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_59,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'LE'(f(suc(suc(C_8))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(suc(C_8))))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_1047,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(suc(suc(C_9))),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(suc(suc(C_9))))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_34,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(B_19),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(B_19))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_1093,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'LE'(f(suc(suc(C_18))),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(suc(C_18))))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_978,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(suc(C_32)),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(suc(C_32)))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_996,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_34),f(suc(B_34))) ) ).

cnf(clause_853,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_62))),s(s(s('0'))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(suc(B_62))))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_927,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(C_31),s('0'))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(C_31))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_44,axiom,
    ( ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(B_43))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_737,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(f(B_73),f(suc(B_73)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'('0',f(suc(suc(B_73))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_73)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72))) ) ).

cnf(clause_1124,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_749,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68))) ) ).

cnf(clause_893,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_986,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(C_20),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(C_20))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_1075,axiom,
    ( ~ 'LE'(f(suc(suc(C_27))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(s('0'),f(suc(suc(C_27))))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_984,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'LE'(f(suc(C_25)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(suc(C_25)))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_813,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(f(B_88),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(B_88))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87)) ) ).

cnf(clause_476,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_759,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_867,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_3)),s('0'))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(suc(C_3)))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_275,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_42))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_897,axiom,
    ( ~ 'LE'(f(C_33),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(C_33))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_284,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_46),f(suc(B_46))) ) ).

cnf(clause_846,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_1))),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(suc(suc(C_1))))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_962,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_54),f(suc(B_54)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_538,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(suc(C_22)),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(suc(C_22)))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_123,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_506,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'LE'(f(B_90),s('0'))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(B_90))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_407,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_42,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_46))))
    | ~ 'E'(f(B_46),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_1008,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_67))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_67))))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_221,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s('0'),f(suc(suc(B_36))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_241,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_77),f(suc(B_77)))
    | ~ 'E'(s('0'),f(suc(suc(B_77))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_601,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_11))),s(s('0')))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(C_11))))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_436,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_33))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(f(B_33),f(suc(B_33)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33))) ) ).

cnf(clause_979,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_3),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(C_3))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_484,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_3)),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_3)))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_9,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68)))
    | iLEQ(suc(B_68),suc(B_68)) ) ).

cnf(clause_3,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | iLEQ(suc(B_45),suc(B_45)) ) ).

cnf(clause_535,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'LE'(f(suc(C_33)),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(suc(C_33)))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_238,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_16))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s('0'),f(suc(suc(C_16))))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_700,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_191,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(f(B_76),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(B_76))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_990,axiom,
    ( ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'('0',f(suc(suc(B_43))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_793,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_1136,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_28,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_13),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(C_13))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_134,axiom,
    ( ~ 'LE'(f(suc(suc(B_28))),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(B_28))))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_1033,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(C_30),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(C_30))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_525,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(B_39),suc(B_39)) ) ).

cnf(clause_848,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(B_63),suc(B_63)) ) ).

cnf(clause_37,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_1071,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_26)),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(suc(C_26)))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_1050,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_30))))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'('0',f(suc(B_29))) ) ).

cnf(clause_205,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'LE'(f(suc(C_15)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(suc(C_15)))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_693,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(B_91),suc(B_91)) ) ).

cnf(clause_112,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_350,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_15),f(suc(B_15))) ) ).

cnf(clause_610,axiom,
    ( ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_182,axiom,
    ( ~ 'LE'(f(C_33),s('0'))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'('0',f(C_33))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_356,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(B_62),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(B_62))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_1086,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_0),f(suc(B_0))) ) ).

cnf(clause_1022,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_352,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'LE'(f(suc(B_71)),s('0'))
    | 'E'('0',f(suc(B_71)))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_688,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'LE'(f(suc(C_28)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(C_28)))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_404,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(B_50),suc(B_50)) ) ).

cnf(clause_769,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57)))) ) ).

cnf(clause_576,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'LE'(f(suc(C_28)),s('0'))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(suc(C_28)))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_411,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_26))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(suc(suc(C_26))))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_88,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(B_89),f(suc(B_89)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | ~ 'E'('0',f(suc(suc(B_89)))) ) ).

cnf(clause_294,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_1)),s(s(s('0'))))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(suc(C_1)))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_728,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(suc(B_67)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(B_67)))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_399,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_1),f(suc(B_1))) ) ).

cnf(clause_557,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_928,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_8),s(s(s('0'))))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(C_8))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_80,axiom,
    ( ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_832,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(C_20),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(C_20))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_1106,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_954,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_48),f(suc(B_48))) ) ).

cnf(clause_375,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(suc(suc(C_19))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(suc(C_19))))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_781,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'LE'(f(suc(C_31)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(C_31)))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_946,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_0),f(suc(B_0))) ) ).

cnf(clause_592,axiom,
    ( ~ 'LE'(f(suc(suc(C_10))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(C_10))))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_103,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_12),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'('0',f(C_12))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_1085,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_14),suc(B_14)) ) ).

cnf(clause_827,axiom,
    ( ~ 'E'('0',f(suc(suc(B_5))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_1142,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(B_49)),s(s('0')))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(B_49)))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_511,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_59),f(suc(B_59))) ) ).

cnf(clause_845,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_1139,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_798,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_323,axiom,
    ( ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_1,axiom,
    ( ~ 'E'('0',f(suc(suc(B_48))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(f(B_48),f(suc(B_48)))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_29,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(B_60),f(suc(B_60))) ) ).

cnf(clause_545,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(f(B_73),f(suc(B_73)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_73))))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'('0',f(suc(B_73)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_817,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(f(B_73),f(suc(B_73)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'('0',f(suc(suc(B_73))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'('0',f(suc(B_73)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72))) ) ).

cnf(clause_1113,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_1)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(C_1)))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_1121,axiom,
    ( ~ 'LE'(f(suc(C_16)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s('0'),f(suc(C_16)))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_797,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'LE'(f(suc(C_6)),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(suc(C_6)))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_402,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_760,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(B_68),suc(B_68)) ) ).

cnf(clause_603,axiom,
    ( ~ 'LE'(f(suc(C)),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(suc(C)))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_473,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_912,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_88),f(suc(B_88))) ) ).

cnf(clause_94,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'(f(B_52),f(suc(B_52))) ) ).

cnf(clause_528,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_1),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(C_1))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_69,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_41),f(suc(B_41))) ) ).

cnf(clause_690,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_397,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_471,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(B_11))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_616,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(B_80),suc(B_80)) ) ).

cnf(clause_527,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s('0'),f(suc(suc(B_36))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_280,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(C_27)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(suc(C_27)))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_692,axiom,
    ( ~ 'LE'(f(suc(C_19)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(suc(C_19)))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_1041,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | iLEQ(suc(B_20),suc(B_20)) ) ).

cnf(clause_174,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'(f(B_88),f(suc(B_88))) ) ).

cnf(clause_622,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_496,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_22),f(suc(B_22))) ) ).

cnf(clause_419,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(C_17),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(C_17))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_780,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_521,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_16))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_16),f(suc(B_16)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_916,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | iLEQ(suc(B_63),suc(B_63)) ) ).

cnf(clause_1062,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_52),f(suc(B_52)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_52))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_843,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_844,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'('0',f(B_92))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_92),f(suc(B_92))) ) ).

cnf(clause_175,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'LE'(f(C_29),s('0'))
    | 'E'('0',f(C_29))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_358,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(f(B_34),f(suc(B_34)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_34))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_85,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'(f(B_51),f(suc(B_51))) ) ).

cnf(clause_331,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_11))),s(s('0')))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(suc(suc(C_11))))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_306,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(C_29)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(suc(C_29)))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_270,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10)))) ) ).

cnf(clause_1109,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_11)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(s('0'),f(suc(C_11)))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_210,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_19))),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(suc(B_19))))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_312,axiom,
    ( ~ 'LE'(f(suc(C)),s(s(s(s(s('0'))))))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(suc(C)))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_1143,axiom,
    ( ~ 'LE'(f(B_74),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_74))
    | 'LE'(f(B_74),s(s('0'))) ) ).

cnf(clause_70,axiom,
    ( ~ 'LE'(f(suc(suc(C_10))),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(suc(suc(C_10))))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_5,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'LE'(f(suc(suc(C_33))),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(suc(suc(C_33))))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_369,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14))) ) ).

cnf(clause_988,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_969,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(suc(C_7)),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_7)))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_283,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14))) ) ).

cnf(clause_509,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s('0'),f(suc(suc(B_51))))
    | ~ 'E'(f(B_51),f(suc(B_51)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_981,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_64))))
    | ~ 'E'(f(B_64),f(suc(B_64)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_615,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | iLEQ(suc(B_14),suc(B_14)) ) ).

cnf(clause_1153,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_66),f(suc(B_66))) ) ).

cnf(clause_696,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_67))),s(s('0')))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(suc(B_67))))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_864,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29))) ) ).

cnf(clause_346,axiom,
    ( ~ 'LE'(f(suc(C_21)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(suc(C_21)))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_1144,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_9)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(suc(C_9)))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_392,axiom,
    ( ~ 'LE'(f(suc(suc(C_14))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_14))))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_342,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'LE'(f(suc(B_90)),s('0'))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(suc(B_90)))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_368,axiom,
    ( ~ 'LE'(f(suc(suc(B_24))),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(B_24))))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_225,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(C_10)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'('0',f(suc(C_10)))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_266,axiom,
    ( ~ 'E'(f(B_0),f(suc(B_0)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B_0))))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_183,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(C_23),s('0'))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(C_23))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_803,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_966,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'LE'(f(suc(suc(C_4))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_4))))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_553,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_7),s('0'))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(C_7))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_648,axiom,
    ( ~ 'LE'(f(suc(C_16)),s(s('0')))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(C_16)))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_591,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'LE'(f(suc(C_13)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_13)))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_222,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_338,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57)))) ) ).

cnf(clause_1118,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_29),suc(B_29)) ) ).

cnf(clause_578,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_11)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(suc(C_11)))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_1057,axiom,
    ( ~ 'E'(f(B_22),f(suc(B_22)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(suc(B_22))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20)) ) ).

cnf(clause_768,axiom,
    ( ~ 'LE'(f(suc(C_33)),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(suc(C_33)))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_600,axiom,
    ( ~ 'LE'(f(suc(suc(C_14))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s(s('0'))),f(suc(suc(C_14))))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_160,axiom,
    ( ~ 'LE'(f(suc(suc(B_86))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_86))))
    | 'LE'(f(B_86),s('0')) ) ).

cnf(clause_1031,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'('0',f(B_92))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(B_92),f(suc(B_92))) ) ).

cnf(clause_885,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'LE'(f(C_2),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(s('0'),f(C_2))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_385,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_23),f(suc(B_23))) ) ).

cnf(clause_1097,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'(f(B_89),f(suc(B_89))) ) ).

cnf(clause_124,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_63,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_516,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_41),f(suc(B_41))) ) ).

cnf(clause_691,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_2))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_2)) ) ).

cnf(clause_143,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_65),f(suc(B_65))) ) ).

cnf(clause_812,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_47),f(suc(B_47)))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s('0'),f(suc(suc(B_47))))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_1099,axiom,
    ( ~ 'LE'(f(suc(suc(C_27))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(suc(suc(C_27))))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_83,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_28))),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(B_28))))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_634,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_5),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(C_5))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_125,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s('0'),f(suc(suc(B_36))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32)) ) ).

cnf(clause_874,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'LE'(f(suc(C_15)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(C_15)))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_327,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(C_30))),s(s('0')))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(suc(suc(C_30))))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_908,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_17))),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(suc(suc(C_17))))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_715,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_58),f(suc(B_58))) ) ).

cnf(clause_478,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_60))))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_60),f(suc(B_60)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_337,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_435,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(f(B_77),f(suc(B_77)))
    | ~ 'E'(s('0'),f(suc(suc(B_77))))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_830,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_1058,axiom,
    ( ~ 'LE'(f(C_14),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s(s('0'))),f(C_14))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_226,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(C_28)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(suc(C_28)))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_220,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_15))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(f(B_15),f(suc(B_15)))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14))) ) ).

cnf(clause_1164,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_23),f(suc(B_23))) ) ).

cnf(clause_307,axiom,
    ( ~ 'LE'(f(C_14),s(s(s(s('0')))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(C_14))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_170,axiom,
    ( ~ 'LE'(f(suc(suc(B_19))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(suc(B_19))))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_285,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'('0',f(suc(suc(B_30))))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_921,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_607,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(B_75),suc(B_75)) ) ).

cnf(clause_918,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_0),s(s(s(s('0')))))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(C_0))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_408,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_82))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'(f(B_82),f(suc(B_82))) ) ).

cnf(clause_460,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'LE'(f(suc(suc(C_13))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(suc(C_13))))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_430,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_911,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(B_28),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(B_28))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_654,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_247,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'LE'(f(C_27),s(s('0')))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(s('0'),f(C_27))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_702,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_64))))
    | ~ 'E'(f(B_64),f(suc(B_64)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63))) ) ).

cnf(clause_77,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_672,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_611,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(B_24),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(B_24))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_958,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(B_38)),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s(s('0'))),f(suc(B_38)))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_935,axiom,
    ( ~ 'LE'(f(C_14),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(C_14))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_231,axiom,
    ( ~ 'LE'(f(suc(suc(B_31))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_31))))
    | 'LE'(f(B_31),s(s(s(s('0'))))) ) ).

cnf(clause_106,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | 'E'(f(A_5),f(suc(A_5)))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_995,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | iLEQ(suc(B_32),suc(B_32)) ) ).

cnf(clause_681,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_3))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_7,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54)))) ) ).

cnf(clause_705,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(B_28),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(B_28))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_168,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | iLEQ(suc(B_50),suc(B_50)) ) ).

cnf(clause_778,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_76),f(suc(B_76))) ) ).

cnf(clause_293,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_121,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_207,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_76),f(suc(B_76))) ) ).

cnf(clause_89,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(B_0),f(suc(B_0))) ) ).

cnf(clause_767,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(C_20))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(suc(C_20))))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_177,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_78),f(suc(B_78))) ) ).

cnf(clause_663,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(B_87),suc(B_87)) ) ).

cnf(clause_290,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'LE'(f(suc(C_6)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(C_6)))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_485,axiom,
    ( ~ 'LE'(f(suc(suc(C_31))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(suc(suc(C_31))))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_502,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_21,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(f(B_47),f(suc(B_47)))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s('0'),f(suc(suc(B_47))))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_446,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_3))),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(suc(suc(C_3))))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_635,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | iLEQ(suc(B_54),suc(B_54)) ) ).

cnf(clause_127,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_66),f(suc(B_66))) ) ).

cnf(clause_140,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_6))),s(s('0')))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(suc(suc(C_6))))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_95,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_36,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_26),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(C_26))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_884,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_35))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_35),f(suc(B_35)))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_22,axiom,
    ( ~ 'LE'(f(C_20),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(C_20))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_128,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_34),f(suc(B_34))) ) ).

cnf(clause_347,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_608,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(B_11))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_86,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(suc(B_83)),s('0'))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(B_83)))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_762,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_8))))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_500,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_25),suc(B_25)) ) ).

cnf(clause_418,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_55,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_301,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_5))),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(suc(C_5))))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_192,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(suc(C_28))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(suc(suc(C_28))))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_609,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_2))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_1133,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(B_1),f(suc(B_1))) ) ).

cnf(clause_0,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_3)),s('0'))
    | 'E'('0',f(suc(C_3)))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_33,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_819,axiom,
    ( ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(suc(B_4))))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_415,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_717,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_66),f(suc(B_66))) ) ).

cnf(clause_758,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'LE'(f(suc(suc(C_13))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(suc(C_13))))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_65,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(C_25),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(C_25))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_518,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_16))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(f(B_16),f(suc(B_16)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14))) ) ).

cnf(clause_81,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87)))
    | iLEQ(suc(B_87),suc(B_87)) ) ).

cnf(clause_1104,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_46))))
    | ~ 'E'(f(B_46),f(suc(B_46)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_753,axiom,
    ( ~ 'E'('0',f(suc(suc(B_5))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_1072,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_991,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_2))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(C_2))))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_861,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_78),f(suc(B_78))) ) ).

cnf(clause_1003,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_624,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'LE'(f(suc(C_10)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_10)))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_413,axiom,
    ( ~ 'E'('0',f(suc(suc(B_55))))
    | ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_332,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(B_85))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_85),f(suc(B_85)))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_739,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_16),f(suc(B_16))) ) ).

cnf(clause_1006,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_1)),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(C_1)))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_467,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'('0',f(suc(suc(B_70))))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68))) ) ).

cnf(clause_539,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(C_27)),s(s('0')))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(C_27)))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_787,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'LE'(f(suc(C_17)),s('0'))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(suc(C_17)))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_1149,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'LE'(f(suc(suc(C_32))),s('0'))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(suc(C_32))))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_377,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_15,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_64))))
    | ~ 'E'(f(B_64),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_410,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(suc(C_16))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(suc(suc(C_16))))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_188,axiom,
    ( ~ 'E'(s('0'),f(suc(B_36)))
    | ~ iLEQ(suc(B_32),suc(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_36))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_1064,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_24))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s(s('0')),f(suc(suc(C_24))))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_439,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(A_5),f(suc(A_5)))
    | iLEQ(suc(B_94),suc(B_94)) ) ).

cnf(clause_562,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_858,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(suc(C_20)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(C_20)))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_495,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_54),f(suc(B_54)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_113,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'('0',f(suc(suc(B_66))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_66),f(suc(B_66)))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_8,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(C_6),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(C_6))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_48,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_65),f(suc(B_65))) ) ).

cnf(clause_507,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_77),f(suc(B_77))) ) ).

cnf(clause_234,axiom,
    ( ~ 'LE'(f(suc(C_30)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(suc(C_30)))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_39,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72)))
    | iLEQ(suc(B_72),suc(B_72)) ) ).

cnf(clause_721,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'LE'(f(suc(C_25)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(suc(C_25)))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_317,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'LE'(f(suc(suc(C_13))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(C_13))))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_840,axiom,
    ( ~ 'LE'(f(suc(suc(B_93))),s('0'))
    | 'E'('0',f(suc(suc(B_93))))
    | 'LE'(f(B_93),'0') ) ).

cnf(clause_517,axiom,
    ( ~ 'E'(f(B_22),f(suc(B_22)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(suc(B_22))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_552,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_28),s('0'))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(C_28))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_139,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_1)),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(suc(C_1)))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_922,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'('0',f(suc(suc(B_30))))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_213,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_46))))
    | ~ 'E'(f(B_46),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_216,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(B_57),suc(B_57)) ) ).

cnf(clause_273,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'(f(B_52),f(suc(B_52))) ) ).

cnf(clause_1141,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_2))),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(suc(suc(C_2))))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_1157,axiom,
    ( ~ 'E'('0',f(suc(suc(B_92))))
    | ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'(f(B_92),f(suc(B_92)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(B_92))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(B_91),f(suc(B_91))) ) ).

cnf(clause_68,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_17))),s('0'))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(suc(suc(C_17))))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_873,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_560,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(B_85))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_85),f(suc(B_85)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_84),f(suc(B_84))) ) ).

cnf(clause_1030,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_71))),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(suc(B_71))))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_957,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_47),f(suc(B_47))) ) ).

cnf(clause_137,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_24))),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(B_24))))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_1091,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_470,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_915,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(B_58),f(suc(B_58))) ) ).

cnf(clause_809,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_0)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(C_0)))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_1156,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_602,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_4,axiom,
    ( ~ 'LE'(f(suc(C_8)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(C_8)))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_829,axiom,
    ( ~ 'LE'(f(suc(suc(C_31))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(suc(C_31))))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_383,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_9),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(C_9))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_351,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(suc(B_62)),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(B_62)))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_135,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_11)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(C_11)))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_561,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(B_54),suc(B_54)) ) ).

cnf(clause_997,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(C_27),s(s('0')))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(C_27))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_644,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_19)),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s('0')),f(suc(B_19)))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_96,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C),s(s(s(s(s('0'))))))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(C))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_871,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | iLEQ(suc(B),suc(B)) ) ).

cnf(clause_149,axiom,
    ( ~ 'LE'(f(suc(B_86)),s(s('0')))
    | 'E'(s('0'),f(suc(B_86)))
    | 'LE'(f(B_86),s('0')) ) ).

cnf(clause_1107,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_6))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_333,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(B_92))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_91),f(suc(B_91)))
    | 'E'(f(B_92),f(suc(B_92))) ) ).

cnf(clause_597,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(suc(C_4))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_4))))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_708,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'LE'(f(suc(C_6)),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(suc(C_6)))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_136,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_501,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_9),f(suc(B_9))) ) ).

cnf(clause_895,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'('0',f(suc(B_73)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72)))
    | 'E'(f(B_73),f(suc(B_73))) ) ).

cnf(clause_914,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | iLEQ(suc(B_68),suc(B_68)) ) ).

cnf(clause_626,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(suc(C_27)),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(s('0'),f(suc(C_27)))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_361,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s('0'),f(suc(suc(B_17))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_1051,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_91),f(suc(B_91)))
    | iLEQ(suc(B_91),suc(B_91)) ) ).

cnf(clause_359,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_31,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_9),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(C_9))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_891,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s('0'),f(suc(suc(B_51))))
    | ~ 'E'(f(B_51),f(suc(B_51)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51))) ) ).

cnf(clause_362,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(C_23),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(C_23))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_709,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_88),f(suc(B_88))) ) ).

cnf(clause_1043,axiom,
    ( ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | iLEQ(suc(B_87),suc(B_87)) ) ).

cnf(clause_111,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_3))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_868,axiom,
    ( ~ 'LE'(f(suc(B_13)),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(B_13)))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_567,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_480,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_71))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(suc(B_71))))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_1083,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_432,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_775,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_15))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(f(B_15),f(suc(B_15)))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_575,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_1002,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(C_25),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s('0'),f(C_25))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_639,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_256,axiom,
    ( ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(A_5))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_559,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_16))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(f(B_16),f(suc(B_16)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_965,axiom,
    ( ~ 'LE'(f(suc(C_12)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'('0',f(suc(C_12)))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_84,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | iLEQ(suc(B_63),suc(B_63)) ) ).

cnf(clause_847,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'LE'(f(suc(suc(B_90))),s('0'))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(suc(suc(B_90))))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_930,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(B_91),f(suc(B_91))) ) ).

cnf(clause_423,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'LE'(f(C_21),s(s('0')))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(C_21))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_1111,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_60))))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_60),f(suc(B_60)))
    | ~ 'E'(s('0'),f(B_60))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_854,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_9),f(suc(B_9))) ) ).

cnf(clause_444,axiom,
    ( ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_334,axiom,
    ( ~ 'LE'(f(B_6),s(s(s(s(s('0'))))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(B_6))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_76,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_267,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_81))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_142,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_565,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'LE'(f(suc(suc(C_0))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_0))))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_955,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(B_79)),s(s('0')))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(suc(B_79)))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_621,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_46),f(suc(B_46))) ) ).

cnf(clause_122,axiom,
    ( ~ 'LE'(f(suc(suc(C))),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(C))))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_251,axiom,
    ( ~ 'LE'(f(suc(suc(C_22))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(suc(C_22))))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_549,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'LE'(f(suc(suc(C_8))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(suc(C_8))))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_537,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_242,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | iLEQ(suc(B_57),suc(B_57)) ) ).

cnf(clause_630,axiom,
    ( ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_405,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_1),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(C_1))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_673,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_40),f(suc(B_40))) ) ).

cnf(clause_414,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_734,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_5),s(s(s('0'))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(C_5))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_1082,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_35))))
    | ~ 'E'(f(B_35),f(suc(B_35)))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_505,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(B_71)),s('0'))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(B_71)))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_937,axiom,
    ( ~ 'LE'(f(suc(suc(C))),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(suc(suc(C))))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_836,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_26)),s('0'))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(C_26)))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_976,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(B_11))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_841,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72)))
    | iLEQ(suc(B_72),suc(B_72)) ) ).

cnf(clause_49,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | ~ 'LE'(f(C_29),s('0'))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(C_29))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_544,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_52),f(suc(B_52)))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_52))))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1017,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_24))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(suc(C_24))))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_694,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'(f(B_88),f(suc(B_88))) ) ).

cnf(clause_824,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_81),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_81))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_777,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(suc(suc(C_23))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(suc(suc(C_23))))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_384,axiom,
    ( ~ 'LE'(f(suc(C_20)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(suc(C_20)))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_279,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87)) ) ).

cnf(clause_931,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_28))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(suc(suc(C_28))))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_309,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s('0'),f(suc(suc(B_51))))
    | ~ 'E'(f(B_51),f(suc(B_51)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_866,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68))) ) ).

cnf(clause_1034,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_1),f(suc(B_1))) ) ).

cnf(clause_313,axiom,
    ( ~ 'E'('0',f(suc(suc(B_92))))
    | ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'(f(B_92),f(suc(B_92)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'('0',f(B_92))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91)) ) ).

cnf(clause_486,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_9)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s('0'))),f(B_9))
    | ~ iLEQ(suc(B_7),suc(B_9))
    | 'E'(f(B_9),f(suc(B_9))) ) ).

cnf(clause_364,axiom,
    ( ~ 'E'('0',f(suc(suc(B_5))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_894,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(B_72),suc(B_72)) ) ).

cnf(clause_38,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(f(B_27),f(suc(B_27)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'('0',f(suc(suc(B_27))))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_104,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_19)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_19)))
    | 'LE'(f(B_19),s(s('0'))) ) ).

cnf(clause_341,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_84),f(suc(B_84)))
    | 'E'(f(B_85),f(suc(B_85))) ) ).

cnf(clause_723,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_2)),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(suc(C_2)))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_900,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_469,axiom,
    ( ~ iLEQ(suc(B_50),suc(B_51))
    | ~ 'E'(s('0'),f(B_51))
    | ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s('0'),f(suc(suc(B_51))))
    | ~ 'E'(f(B_51),f(suc(B_51)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_51)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_799,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'LE'(f(C_6),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s('0'),f(C_6))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_590,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_22),f(suc(B_22))) ) ).

cnf(clause_580,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_670,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_1020,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | iLEQ(suc(B_20),suc(B_20)) ) ).

cnf(clause_108,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_11),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(C_11))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_1067,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s('0'),f(suc(suc(B_42))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s('0'),f(B_42))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(s('0'),f(suc(B_42)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_42)) ) ).

cnf(clause_163,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_28)),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(B_28)))
    | 'LE'(f(B_28),'0') ) ).

cnf(clause_18,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_94),f(suc(B_94)))
    | iLEQ(suc(B_94),suc(B_94)) ) ).

cnf(clause_53,axiom,
    ( ~ 'LE'(f(suc(suc(C_31))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(suc(suc(C_31))))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_382,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(C_17),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'('0',f(C_17))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_261,axiom,
    ( ~ 'E'('0',f(suc(suc(B_48))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(f(B_48),f(suc(B_48)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_968,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_58))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_58),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_378,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ 'LE'(f(suc(C_23)),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(C_23)))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_148,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_16))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_16),f(suc(B_16)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_200,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_4)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(C_4)))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_876,axiom,
    ( ~ 'LE'(f(B_83),s('0'))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(B_83))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_588,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_465,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'LE'(f(suc(suc(C_21))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(suc(C_21))))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_701,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_44))),s(s(s('0'))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(suc(B_44))))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_776,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_619,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_24),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(C_24))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_178,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32)) ) ).

cnf(clause_379,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_394,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(B_7),f(suc(B_7))) ) ).

cnf(clause_426,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_22),s('0'))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(C_22))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_66,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_850,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_860,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'LE'(f(suc(C_17)),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(C_17)))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_953,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'('0',f(suc(suc(B_78))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_78),f(suc(B_78)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_54,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_17))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(suc(C_17))))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_959,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(B_4)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_4))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_4))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_973,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(suc(C_14)),s(s(s(s('0')))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(suc(C_14)))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_74,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'LE'(f(suc(C_6)),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(C_6)))
    | 'LE'(f(C_6),s('0')) ) ).

cnf(clause_105,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_33),f(suc(B_33))) ) ).

cnf(clause_1079,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_46))))
    | ~ 'E'(f(B_46),f(suc(B_46)))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45))) ) ).

cnf(clause_1078,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_20),suc(B_20)) ) ).

cnf(clause_741,axiom,
    ( ~ 'LE'(f(suc(suc(C_10))),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'('0',f(suc(suc(C_10))))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_880,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(B_38)),s(s(s(s('0')))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(suc(B_38)))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_278,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | iLEQ(suc(B_75),suc(B_75)) ) ).

cnf(clause_631,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_1110,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | iLEQ(suc(B_14),suc(B_14)) ) ).

cnf(clause_224,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'LE'(f(suc(suc(C_21))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(suc(C_21))))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_488,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | iLEQ(suc(B),suc(B)) ) ).

cnf(clause_901,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ 'E'(f(B_40),f(suc(B_40)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_40))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_835,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_26)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(suc(C_26)))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_1026,axiom,
    ( ~ 'LE'(f(suc(C)),s(s(s(s(s('0'))))))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(suc(C)))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_947,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(B_67),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(B_67))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_1094,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(B_71),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(B_71))
    | 'LE'(f(B_71),'0') ) ).

cnf(clause_896,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | iLEQ(suc(B_7),suc(B_7)) ) ).

cnf(clause_945,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'LE'(f(suc(suc(C_29))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(suc(suc(C_29))))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_618,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'('0',f(suc(suc(B_43))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43)) ) ).

cnf(clause_304,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_77),f(suc(B_77)))
    | ~ 'E'(s('0'),f(suc(suc(B_77))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_1092,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'LE'(f(suc(C_33)),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'('0',f(suc(C_33)))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_1052,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_3),s('0'))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(C_3))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_641,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'LE'(f(suc(C_15)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s('0')),f(suc(C_15)))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_243,axiom,
    ( ~ 'E'('0',f(suc(suc(B_55))))
    | ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_606,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_41),f(suc(B_41))) ) ).

cnf(clause_23,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_967,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20)) ) ).

cnf(clause_1163,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'LE'(f(C_2),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(C_2))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_319,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_1))),s(s(s('0'))))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s('0')),f(suc(suc(C_1))))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_187,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_913,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_929,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_5))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(C_5))))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_992,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(suc(C_18))),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(suc(suc(C_18))))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_1015,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_16))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s('0')),f(suc(B_16)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s('0')),f(B_16))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_16),f(suc(B_16))) ) ).

cnf(clause_246,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | iLEQ(suc(B_25),suc(B_25)) ) ).

cnf(clause_288,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_30))))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_646,axiom,
    ( ~ 'LE'(f(suc(C_23)),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(suc(C_23)))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_1018,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_15))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(suc(suc(C_15))))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_400,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_7))),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(suc(suc(C_7))))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_265,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_73)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_73),f(suc(B_73))) ) ).

cnf(clause_50,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_2))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_1060,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'LE'(f(suc(C_14)),s(s(s(s('0')))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(suc(C_14)))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_943,axiom,
    ( ~ 'E'('0',f(suc(suc(B_5))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_5))
    | ~ 'E'('0',f(suc(B_5)))
    | ~ 'E'('0',f(B_5)) ) ).

cnf(clause_482,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_8),s(s(s('0'))))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(s(s('0')),f(C_8))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_1089,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_254,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_35))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_35),f(suc(B_35)))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32)) ) ).

cnf(clause_328,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_52),f(suc(B_52))) ) ).

cnf(clause_132,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_3))),s('0'))
    | 'E'('0',f(suc(suc(C_3))))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_180,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'('0',f(suc(suc(B_66))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_66),f(suc(B_66)))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63))) ) ).

cnf(clause_629,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | iLEQ(suc(B_75),suc(B_75)) ) ).

cnf(clause_109,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_821,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(B_94),f(suc(B_94)))
    | 'E'(f(B_95),f(suc(B_95))) ) ).

cnf(clause_587,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_571,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C_3),s('0'))
    | 'E'('0',f(C_3))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_1155,axiom,
    ( ~ 'LE'(f(suc(B_53)),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(B_53)))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_782,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_4)),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(suc(C_4)))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_573,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_85))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_85),f(suc(B_85)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_84),f(suc(B_84))) ) ).

cnf(clause_899,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(f(B_65),f(suc(B_65)))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s('0'),f(suc(suc(B_65))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_78,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(suc(C_22)),s('0'))
    | 'E'('0',f(suc(C_22)))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_336,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(C_29)),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(C_29)))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_733,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_3))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3))) ) ).

cnf(clause_998,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_84),f(suc(B_84)))
    | 'E'(f(B_85),f(suc(B_85))) ) ).

cnf(clause_1049,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_345,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_3))),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(suc(C_3))))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_208,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_9)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(C_9)))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_195,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_34))
    | ~ iLEQ(suc(B_32),suc(B_34))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_34)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_34),f(suc(B_34))) ) ).

cnf(clause_1040,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(B_84),suc(B_84)) ) ).

cnf(clause_292,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'LE'(f(suc(suc(C_33))),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'('0',f(suc(suc(C_33))))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_1126,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_21))))
    | ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_422,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_13)),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(B_13)))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_373,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(B_44),s(s(s('0'))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(B_44))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_380,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_477,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(suc(suc(C_15))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s(s('0')),f(suc(suc(C_15))))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_198,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_2)),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(C_2)))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_1166,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(C_18)),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(suc(C_18)))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_151,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_4)),s(s(s(s('0')))))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(suc(C_4)))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_555,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_64),f(suc(B_64))) ) ).

cnf(clause_1137,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_11),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(s('0'),f(C_11))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_617,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(suc(C_32)),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(C_32)))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_563,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_960,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_78),f(suc(B_78))) ) ).

cnf(clause_87,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(suc(suc(C_19))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(suc(C_19))))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_264,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_19),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(C_19))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_926,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(B_24)),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(B_24)))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_1140,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(suc(suc(C_32))),s('0'))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(suc(suc(C_32))))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_791,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(C_18)),s(s(s('0'))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(suc(C_18)))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_298,axiom,
    ( ~ 'LE'(f(B_31),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B_31))
    | 'LE'(f(B_31),s(s(s(s('0'))))) ) ).

cnf(clause_625,axiom,
    ( ~ 'E'('0',f(suc(suc(B_92))))
    | ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'(f(B_92),f(suc(B_92)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'('0',f(suc(B_92)))
    | ~ 'E'('0',f(B_92))
    | ~ iLEQ(suc(B_91),suc(B_92))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_91),f(suc(B_91))) ) ).

cnf(clause_429,axiom,
    ( ~ 'E'('0',f(suc(B_82)))
    | ~ 'E'(f(B_82),f(suc(B_82)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_82))
    | ~ 'E'('0',f(suc(suc(B_82))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ iLEQ(suc(B_80),suc(B_82))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_814,axiom,
    ( ~ 'LE'(f(suc(C_12)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(suc(C_12)))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_570,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_651,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_2))),s(s('0')))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(suc(C_2))))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_357,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(suc(suc(C_0))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_0))))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_45,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(B_89),f(suc(B_89)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | ~ 'E'('0',f(suc(suc(B_89))))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_842,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_28),s('0'))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(C_28))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_447,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(f(B_88),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(B_88))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_14,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_887,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_85),f(suc(B_85))) ) ).

cnf(clause_1065,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | iLEQ(suc(A_0),suc(A_0)) ) ).

cnf(clause_491,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(suc(suc(B_83))),s('0'))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(suc(B_83))))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_156,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_15))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(f(B_15),f(suc(B_15)))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_540,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_48),f(suc(B_48))) ) ).

cnf(clause_1024,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_804,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(C_4),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(C_4))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_1165,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_84),f(suc(B_84))) ) ).

cnf(clause_748,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_33))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(f(B_33),f(suc(B_33)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_569,axiom,
    ( ~ 'LE'(f(suc(suc(B_74))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_74))))
    | 'LE'(f(B_74),s(s('0'))) ) ).

cnf(clause_43,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(C_25),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(C_25))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_258,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'LE'(f(C_17),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(C_17))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_839,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s('0'),f(B_60))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_60),f(suc(B_60))) ) ).

cnf(clause_245,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_1114,axiom,
    ( ~ 'LE'(f(C_16),s(s('0')))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(C_16))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_532,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'LE'(f(C_2),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(C_2))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_816,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(B_83))),s('0'))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(suc(B_83))))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_789,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_7))),s('0'))
    | 'E'('0',f(suc(suc(C_7))))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_305,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_23),f(suc(B_23)))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_23))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_1054,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80))) ) ).

cnf(clause_548,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(f(B_77),f(suc(B_77)))
    | ~ 'E'(s('0'),f(suc(suc(B_77))))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_735,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_59))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(f(B_59),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_810,axiom,
    ( ~ 'LE'(f(C_10),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(C_10))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_197,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(B_6))),s(s(s(s(s('0'))))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_1127,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'('0',f(B_43))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'('0',f(suc(suc(B_43))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_43)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ iLEQ(suc(B_39),suc(B_43))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1076,axiom,
    ( ~ iLEQ(suc(B_80),suc(B_81))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_81)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_81))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_81),f(suc(B_81))) ) ).

cnf(clause_16,axiom,
    ( ~ 'E'('0',f(suc(suc(B_55))))
    | ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'('0',f(suc(B_55)))
    | ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'('0',f(B_55))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(suc(suc(B_54))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1016,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_58))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_58),f(suc(B_58)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57)))) ) ).

cnf(clause_202,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_84),f(suc(B_84)))
    | iLEQ(suc(B_84),suc(B_84)) ) ).

cnf(clause_1035,axiom,
    ( ~ iLEQ(suc(B_14),suc(B_17))
    | ~ 'E'(s('0'),f(B_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(suc(B_17)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s('0'),f(suc(suc(B_17))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_514,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_58))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_58),f(suc(B_58)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_568,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_91))))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_91),f(suc(B_91)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91)) ) ).

cnf(clause_823,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(B_67),s(s('0')))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(B_67))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_56,axiom,
    ( ~ 'LE'(f(C_10),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'('0',f(C_10))
    | 'LE'(f(C_10),'0') ) ).

cnf(clause_490,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(B_94),f(suc(B_94)))
    | iLEQ(suc(B_94),suc(B_94)) ) ).

cnf(clause_779,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_2)),s(s('0')))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s('0'),f(suc(C_2)))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_687,axiom,
    ( ~ 'LE'(f(suc(B_24)),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(suc(B_24)))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_605,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_28),s('0'))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'('0',f(C_28))
    | 'LE'(f(C_28),'0') ) ).

cnf(clause_794,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_671,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_60))))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_60),f(suc(B_60)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57))) ) ).

cnf(clause_326,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | iLEQ(suc(B_39),suc(B_39)) ) ).

cnf(clause_167,axiom,
    ( ~ 'E'(f(B_1),f(suc(B_1)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_1))))
    | ~ 'E'(s(s(s(s('0')))),f(B_1)) ) ).

cnf(clause_25,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_12),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(C_12))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_133,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'LE'(f(C_27),s(s('0')))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(C_27))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_118,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(C_32),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(C_32))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_131,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'('0',f(suc(suc(B_12))))
    | ~ 'E'('0',f(B_12)) ) ).

cnf(clause_181,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B)))) ) ).

cnf(clause_372,axiom,
    ( ~ 'LE'(f(suc(suc(B_13))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(suc(B_13))))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_676,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_7),s('0'))
    | 'E'('0',f(C_7))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_907,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_1)))
    | ~ iLEQ(suc(B),suc(B_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_1))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_1),f(suc(B_1))) ) ).

cnf(clause_726,axiom,
    ( ~ 'LE'(f(suc(C_12)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(suc(C_12)))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_865,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_64))))
    | ~ 'E'(f(B_64),f(suc(B_64)))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1036,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_25))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(s('0'),f(suc(suc(C_25))))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_119,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_851,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'LE'(f(suc(suc(C_18))),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(suc(suc(C_18))))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_1009,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_21))))
    | ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_145,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(suc(C_1))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(C_1))))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_291,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_26),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'('0',f(C_26))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_35,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(C))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_186,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | iLEQ(suc(B_80),suc(B_80)) ) ).

cnf(clause_716,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1011,axiom,
    ( ~ 'E'('0',f(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_20),suc(B_23))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_23),f(suc(B_23)))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'('0',f(suc(B_23)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(suc(suc(B_23))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20)) ) ).

cnf(clause_581,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(C_24))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(suc(suc(C_24))))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_655,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'LE'(f(C_23),s('0'))
    | 'E'('0',f(C_23))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_1115,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C),s(s(s(s(s('0'))))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(C))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_890,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(B_94))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_94),f(suc(B_94))) ) ).

cnf(clause_925,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(C_30),s(s('0')))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(C_30))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_526,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_59))))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(f(B_59),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_59))
    | ~ 'E'(s(s('0')),f(B_59))
    | ~ 'E'(s(s('0')),f(suc(B_59)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_706,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'LE'(f(suc(C_5)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s('0')),f(suc(C_5)))
    | 'LE'(f(C_5),s(s('0'))) ) ).

cnf(clause_747,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_15)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ iLEQ(suc(B_14),suc(B_15))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_15))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(f(B_15),f(suc(B_15))) ) ).

cnf(clause_169,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_11)),s(s('0')))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(suc(C_11)))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_483,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(suc(B_95))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(B_95),f(suc(B_95)))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_956,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_184,axiom,
    ( ~ 'E'(s('0'),f(suc(B_60)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_60))))
    | ~ iLEQ(suc(B_57),suc(B_60))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_60),f(suc(B_60)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(B_60))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57)))) ) ).

cnf(clause_878,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_77))
    | ~ 'E'(s('0'),f(suc(B_77)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(B_75),suc(B_77))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_77),f(suc(B_77))) ) ).

cnf(clause_674,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_11))),s(s('0')))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(s('0'),f(suc(suc(C_11))))
    | 'LE'(f(C_11),s('0')) ) ).

cnf(clause_1105,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_89),f(suc(B_89))) ) ).

cnf(clause_115,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(f(B_76),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(B_76))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_451,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'LE'(f(suc(suc(C_12))),s('0'))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(suc(suc(C_12))))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_443,axiom,
    ( ~ 'LE'(f(suc(B_44)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(suc(B_44)))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_707,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(B_49)),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(B_49)))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_12,axiom,
    ( ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_48),f(suc(B_48))) ) ).

cnf(clause_594,axiom,
    ( ~ 'LE'(f(suc(suc(C_14))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_14))))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_228,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_2)))
    | ~ 'E'(s(s(s('0'))),f(B_2))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ iLEQ(suc(B),suc(B_2))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_934,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_3)),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(suc(C_3)))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_766,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'LE'(f(suc(suc(C_29))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'('0',f(suc(suc(C_29))))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_1032,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'LE'(f(suc(C_18)),s(s(s('0'))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s(s('0')),f(suc(C_18)))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_162,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_7),suc(B_11))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_679,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(C_30))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(suc(suc(C_30))))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_60,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(C_8),s(s(s('0'))))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(C_8))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_355,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_951,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'LE'(f(suc(C_17)),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'('0',f(suc(C_17)))
    | 'LE'(f(C_17),'0') ) ).

cnf(clause_712,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_909,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'('0',f(suc(suc(B_78))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_78),f(suc(B_78)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_339,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_7))),s('0'))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(suc(suc(C_7))))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_515,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_64),f(suc(B_64))) ) ).

cnf(clause_513,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_52),f(suc(B_52)))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_52))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52)) ) ).

cnf(clause_1028,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C_3),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(C_3))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_859,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_47),f(suc(B_47))) ) ).

cnf(clause_295,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_47),f(suc(B_47))) ) ).

cnf(clause_93,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'LE'(f(suc(C_15)),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(suc(C_15)))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_604,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(B_62)),s(s(s('0'))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(B_62)))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_1159,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_920,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'LE'(f(z),'0')
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39))) ) ).

cnf(clause_805,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(suc(C_25))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s('0'),f(suc(suc(C_25))))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_239,axiom,
    ( ~ 'LE'(f(suc(C_21)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(suc(C_21)))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_667,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_66))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'('0',f(suc(B_66)))
    | ~ 'E'('0',f(suc(suc(B_66))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_66),f(suc(B_66)))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ iLEQ(suc(B_63),suc(B_66))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_746,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_54),f(suc(B_54)))
    | iLEQ(suc(B_54),suc(B_54)) ) ).

cnf(clause_211,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(B_62),s(s(s('0'))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(B_62))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_159,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_33))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(f(B_33),f(suc(B_33)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(B_32),f(suc(B_32))) ) ).

cnf(clause_276,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_474,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(B_6),s(s(s(s(s('0'))))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(B_6))
    | 'LE'(f(B_6),s(s(s(s('0'))))) ) ).

cnf(clause_126,axiom,
    ( ~ 'LE'(f(suc(suc(C_33))),s('0'))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_87),f(suc(B_87)))
    | 'E'('0',f(suc(suc(C_33))))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_449,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | iLEQ(suc(B),suc(B)) ) ).

cnf(clause_343,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_64),f(suc(B_64))) ) ).

cnf(clause_1116,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_80),f(suc(B_80)))
    | iLEQ(suc(B_80),suc(B_80)) ) ).

cnf(clause_17,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(suc(B_62))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s(s('0')),f(suc(suc(B_62))))
    | 'LE'(f(B_62),s(s('0'))) ) ).

cnf(clause_263,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72))) ) ).

cnf(clause_906,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(B_79))),s(s('0')))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(suc(suc(B_79))))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_807,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'('0',f(suc(B_12)))
    | ~ iLEQ(suc(B_7),suc(B_12))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'('0',f(B_12))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_100,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'LE'(f(C_4),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'(s(s(s('0'))),f(C_4))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_745,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(f(B_65),f(suc(B_65))) ) ).

cnf(clause_308,axiom,
    ( ~ 'LE'(f(suc(suc(C_16))),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(suc(suc(C_16))))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_881,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_19),s(s('0')))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s('0'),f(C_19))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_870,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_303,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_94),f(suc(B_94)))
    | 'E'(f(B_95),f(suc(B_95))) ) ).

cnf(clause_24,axiom,
    ( ~ 'LE'(f(B_56),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_56))
    | 'LE'(f(B_56),s(s(s('0')))) ) ).

cnf(clause_637,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(B_53),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(B_53))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_833,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_462,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'LE'(f(suc(suc(C_4))),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(suc(C_4))))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_1150,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_50))
    | ~ iLEQ(suc(B_50),suc(B_52))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'('0',f(suc(B_52)))
    | ~ 'E'(f(B_52),f(suc(B_52)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_52))))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'('0',f(B_52))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_50),f(suc(B_50))) ) ).

cnf(clause_193,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(f(B_73),f(suc(B_73)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_73))))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_73)))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_172,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(C_31),s('0'))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(C_31))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_1128,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(B_38),s(s(s(s('0')))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(B_38))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_146,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(B_80),suc(B_80)) ) ).

cnf(clause_1073,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20)))
    | iLEQ(suc(B_20),suc(B_20)) ) ).

cnf(clause_281,axiom,
    ( ~ 'E'(s('0'),f(B_88))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(f(B_88),f(suc(B_88)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ iLEQ(suc(B_87),suc(B_88))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(B_88))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_472,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(C_25),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(C_25))
    | 'LE'(f(C_25),s('0')) ) ).

cnf(clause_227,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_666,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(C_7),s('0'))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_7),f(suc(B_7)))
    | 'E'('0',f(C_7))
    | 'LE'(f(C_7),'0') ) ).

cnf(clause_296,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(C_18),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(C_18))
    | 'LE'(f(C_18),s(s('0'))) ) ).

cnf(clause_933,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s('0')),f(suc(B_46)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_46))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(B_45),suc(B_46))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_46),f(suc(B_46))) ) ).

cnf(clause_442,axiom,
    ( ~ 'LE'(f(C_15),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(C_15))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_201,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'('0',f(B_48))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_48)))
    | ~ iLEQ(suc(B_45),suc(B_48))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_48),f(suc(B_48))) ) ).

cnf(clause_856,axiom,
    ( ~ 'E'(f(B_22),f(suc(B_22)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_22))
    | ~ 'E'(s('0'),f(suc(suc(B_22))))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s('0'),f(suc(B_22)))
    | ~ iLEQ(suc(B_20),suc(B_22))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_999,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_21))))
    | ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20))) ) ).

cnf(clause_989,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_12),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'('0',f(C_12))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_374,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'LE'(f(suc(C_14)),s(s(s(s('0')))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(suc(C_14)))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_970,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_13,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_475,axiom,
    ( ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(B_20),f(suc(B_20)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_1021,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(z),'0')
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_185,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_8))))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | ~ 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_704,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(B_21))))
    | ~ 'E'(s(s('0')),f(B_21))
    | ~ iLEQ(suc(B_20),suc(B_21))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(s(s('0')),f(suc(B_21)))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s(s('0')),f(B_20)) ) ).

cnf(clause_310,axiom,
    ( ~ 'LE'(f(C_20),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(C_20))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_424,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_47)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ 'E'(s('0'),f(B_47))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ iLEQ(suc(B_45),suc(B_47))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(f(B_47),f(suc(B_47))) ) ).

cnf(clause_661,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ iLEQ(suc(B_7),suc(B_10))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_459,axiom,
    ( ~ 'LE'(f(suc(suc(C_22))),s('0'))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'('0',f(suc(suc(C_22))))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_754,axiom,
    ( ~ 'LE'(f(C_33),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'('0',f(C_33))
    | 'LE'(f(C_33),'0') ) ).

cnf(clause_765,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_8))))
    | ~ iLEQ(suc(B_7),suc(B_8))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_8)))
    | ~ 'E'(s(s(s(s('0')))),f(B_8))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_32,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_92,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(B_32),suc(B_32)) ) ).

cnf(clause_57,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(B_83)),s('0'))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'('0',f(suc(B_83)))
    | 'LE'(f(B_83),'0') ) ).

cnf(clause_154,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(C_15),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(C_15))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_675,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(suc(C_3))),s('0'))
    | 'E'(f(B),f(suc(B)))
    | 'E'('0',f(suc(suc(C_3))))
    | 'LE'(f(C_3),'0') ) ).

cnf(clause_166,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(B_67)),s(s('0')))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(B_67)))
    | 'LE'(f(B_67),s('0')) ) ).

cnf(clause_722,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_76),f(suc(B_76))) ) ).

cnf(clause_718,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_95),f(suc(B_95))) ) ).

cnf(clause_656,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'LE'(f(B_24),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s('0'),f(B_24))
    | 'LE'(f(B_24),s('0')) ) ).

cnf(clause_649,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(B_38))),s(s(s(s('0')))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s(s('0'))),f(suc(suc(B_38))))
    | 'LE'(f(B_38),s(s(s('0')))) ) ).

cnf(clause_713,axiom,
    ( ~ 'LE'(f(suc(B_93)),s('0'))
    | 'E'('0',f(suc(B_93)))
    | 'LE'(f(B_93),'0') ) ).

cnf(clause_1005,axiom,
    ( ~ 'E'('0',f(suc(B_91)))
    | ~ 'E'('0',f(B_91))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_91))
    | 'E'(f(B_91),f(suc(B_91)))
    | iLEQ(suc(B_91),suc(B_91)) ) ).

cnf(clause_613,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_689,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(C_30),s(s('0')))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(s('0'),f(C_30))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_1119,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'LE'(f(suc(C_29)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68)))
    | 'E'('0',f(suc(C_29)))
    | 'LE'(f(C_29),'0') ) ).

cnf(clause_190,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_4)),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(suc(C_4)))
    | 'LE'(f(C_4),s(s(s('0')))) ) ).

cnf(clause_248,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(B_75),suc(B_75)) ) ).

cnf(clause_464,axiom,
    ( ~ 'LE'(f(B_79),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(s('0'),f(B_79))
    | 'LE'(f(B_79),s('0')) ) ).

cnf(clause_905,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_24)),s(s(s('0'))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(suc(C_24)))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_586,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(f(B_65),f(suc(B_65)))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s('0'),f(suc(suc(B_65))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63))) ) ).

cnf(clause_698,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_980,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(B_53),s('0'))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(B_53))
    | 'LE'(f(B_53),'0') ) ).

cnf(clause_530,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_68),f(suc(B_68)))
    | iLEQ(suc(B_68),suc(B_68)) ) ).

cnf(clause_534,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ 'E'(f(B_40),f(suc(B_40)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_40))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1027,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(suc(C_2)),s(s('0')))
    | 'E'(s('0'),f(suc(C_2)))
    | 'LE'(f(C_2),s('0')) ) ).

cnf(clause_157,axiom,
    ( ~ 'LE'(f(suc(C_21)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(B_45))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(f(B_45),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(suc(C_21)))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_533,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'LE'(f(C),s(s(s(s(s('0'))))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s(s('0')))),f(C))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_282,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'LE'(f(suc(suc(C_8))),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s(s('0')),f(suc(suc(C_8))))
    | 'LE'(f(C_8),s(s('0'))) ) ).

cnf(clause_1066,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63))) ) ).

cnf(clause_725,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_12),s('0'))
    | ~ 'E'(s(s('0')),f(suc(B_20)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_20))
    | ~ 'E'(f(B_20),f(suc(B_20)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_20))))
    | ~ 'E'(s(s('0')),f(B_20))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'('0',f(C_12))
    | 'LE'(f(C_12),'0') ) ).

cnf(clause_520,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'(f(B_78),f(suc(B_78))) ) ).

cnf(clause_262,axiom,
    ( ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(C_1),s(s(s('0'))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | 'E'(s(s('0')),f(C_1))
    | 'LE'(f(C_1),s(s('0'))) ) ).

cnf(clause_387,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_61))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_1100,axiom,
    ( ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'LE'(f(C_15),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s(s('0')),f(C_15))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_948,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_73))
    | ~ 'E'('0',f(B_72))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(B_72),suc(B_73))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_73)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_72),f(suc(B_72)))
    | 'E'(f(B_73),f(suc(B_73))) ) ).

cnf(clause_512,axiom,
    ( ~ 'LE'(f(suc(C_30)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(suc(C_30)))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_360,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'LE'(f(B_13),s(s(s(s('0')))))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(s(s(s('0'))),f(B_13))
    | 'LE'(f(B_13),s(s(s('0')))) ) ).

cnf(clause_335,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(B_76)))
    | ~ 'E'(f(B_76),f(suc(B_76)))
    | ~ 'E'(s(s('0')),f(B_76))
    | ~ iLEQ(suc(B_75),suc(B_76))
    | ~ 'E'(s(s('0')),f(suc(suc(B_76))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_1087,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(B_72))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_72),f(suc(B_72)))
    | ~ 'E'('0',f(suc(suc(B_72))))
    | ~ iLEQ(suc(A_2),suc(B_72))
    | ~ 'E'('0',f(suc(B_72)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1019,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(B_89),f(suc(B_89)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | ~ 'E'('0',f(suc(suc(B_89))))
    | 'E'(f(B_87),f(suc(B_87))) ) ).

cnf(clause_250,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1025,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(B_50))))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(f(B_50),f(suc(B_50)))
    | ~ 'LE'(f(suc(suc(C_23))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(suc(C_23))))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_659,axiom,
    ( ~ 'E'(f(B_0),f(suc(B_0)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B_0))))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B))) ) ).

cnf(clause_461,axiom,
    ( ~ 'LE'(f(suc(suc(C))),s(s(s(s(s('0'))))))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s(s('0')))),f(suc(suc(C))))
    | 'LE'(f(C),s(s(s(s('0'))))) ) ).

cnf(clause_872,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_94))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(B_94)))
    | ~ 'E'('0',f(suc(suc(B_94))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(B_94),f(suc(B_94)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ iLEQ(suc(B_94),suc(B_95))
    | ~ 'E'('0',f(B_94))
    | ~ 'E'('0',f(suc(B_95)))
    | ~ 'E'('0',f(B_95))
    | 'E'(f(B_95),f(suc(B_95))) ) ).

cnf(clause_428,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_24)),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(suc(C_24)))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_440,axiom,
    ( ~ 'LE'(f(suc(C_23)),s('0'))
    | ~ iLEQ(suc(A_1),suc(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(B_50))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_50)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_50),f(suc(B_50)))
    | 'E'('0',f(suc(C_23)))
    | 'LE'(f(C_23),'0') ) ).

cnf(clause_141,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_14))))
    | ~ iLEQ(suc(B_14),suc(B_18))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_18))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_584,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_19),s(s('0')))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(C_19))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_26,axiom,
    ( ~ 'LE'(f(C_16),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(s('0'),f(C_16))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_731,axiom,
    ( ~ 'E'(s(s('0')),f(B_64))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ iLEQ(suc(B_63),suc(B_64))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s(s('0')),f(suc(B_64)))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_64),f(suc(B_64))) ) ).

cnf(clause_1037,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(f(B_65),f(suc(B_65)))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s('0'),f(suc(suc(B_65))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_302,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'LE'(f(suc(C_0)),s(s(s(s('0')))))
    | 'E'(f(B),f(suc(B)))
    | 'E'(s(s(s('0'))),f(suc(C_0)))
    | 'LE'(f(C_0),s(s(s('0')))) ) ).

cnf(clause_395,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(suc(suc(C_20))),s('0'))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'('0',f(suc(suc(C_20))))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_750,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_80),f(suc(B_80)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'LE'(f(suc(suc(C_32))),s('0'))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(B_80))))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'('0',f(suc(suc(C_32))))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_820,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(suc(suc(C_30))),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(suc(B_75))))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(f(B_75),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(s('0'),f(suc(suc(C_30))))
    | 'LE'(f(C_30),s('0')) ) ).

cnf(clause_785,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_40))
    | ~ 'E'(s(s(s('0'))),f(suc(B_40)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(B_39),suc(B_40))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(f(B_40),f(suc(B_40))) ) ).

cnf(clause_1012,axiom,
    ( ~ iLEQ(suc(B_32),suc(B_37))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_32),f(suc(B_32)))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_32))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32)) ) ).

cnf(clause_41,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(suc(suc(C_15))),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s('0')),f(suc(suc(C_15))))
    | 'LE'(f(C_15),s(s('0'))) ) ).

cnf(clause_62,axiom,
    ( ~ 'E'('0',f(B_84))
    | ~ iLEQ(suc(A_3),suc(B_84))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(B_84))))
    | ~ 'E'('0',f(suc(suc(B_85))))
    | ~ 'E'('0',f(suc(B_85)))
    | ~ 'E'(f(B_85),f(suc(B_85)))
    | ~ 'E'(f(B_84),f(suc(B_84)))
    | ~ iLEQ(suc(B_84),suc(B_85))
    | ~ 'E'('0',f(suc(B_84)))
    | ~ 'E'('0',f(B_85))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_321,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'LE'(f(suc(C_13)),s('0'))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'('0',f(suc(C_13)))
    | 'LE'(f(C_13),'0') ) ).

cnf(clause_1045,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_24),s(s(s('0'))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(s(s('0')),f(C_24))
    | 'LE'(f(C_24),s(s('0'))) ) ).

cnf(clause_1146,axiom,
    ( ~ 'LE'(f(C_16),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s('0'),f(C_16))
    | 'LE'(f(C_16),s('0')) ) ).

cnf(clause_1077,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_29))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'('0',f(suc(suc(B_29))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'('0',f(B_29))
    | ~ 'E'('0',f(suc(B_30)))
    | ~ 'E'('0',f(B_30))
    | ~ 'E'('0',f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_678,axiom,
    ( ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(B),suc(B_3))
    | ~ 'E'(s(s('0')),f(B_3))
    | ~ 'E'(s(s('0')),f(suc(B_3)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B),f(suc(B)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_938,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_19),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_39),f(suc(B_39)))
    | 'E'(s('0'),f(C_19))
    | 'LE'(f(C_19),s('0')) ) ).

cnf(clause_1013,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(s('0'),f(suc(B_26)))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_26),f(suc(B_26))) ) ).

cnf(clause_772,axiom,
    ( ~ iLEQ(suc(A_0),suc(B_7))
    | ~ 'E'(f(B_7),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_7))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(B_7))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_7)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_2,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | iLEQ(suc(B_45),suc(B_45)) ) ).

cnf(clause_452,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_35)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(B_32),suc(B_35))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(s(s('0')),f(B_35))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_35),f(suc(B_35))) ) ).

cnf(clause_822,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'LE'(f(z),'0')
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'('0',f(suc(B_54)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(B_54))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_650,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ iLEQ(suc(B_32),suc(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(B_33))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_33)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(f(B_33),f(suc(B_33))) ) ).

cnf(clause_582,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'LE'(f(B_90),s('0'))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'('0',f(B_90))
    | 'LE'(f(B_90),'0') ) ).

cnf(clause_596,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | iLEQ(suc(B_57),suc(B_57)) ) ).

cnf(clause_71,axiom,
    ( ~ 'LE'(f(suc(suc(C_27))),s(s('0')))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_63))))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(f(B_63),f(suc(B_63)))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(s('0'),f(suc(suc(C_27))))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_828,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'LE'(f(suc(C_26)),s('0'))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'('0',f(suc(C_26)))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_564,axiom,
    ( ~ iLEQ(suc(B_63),suc(B_65))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(f(B_65),f(suc(B_65)))
    | ~ 'E'(s('0'),f(suc(B_65)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s('0'),f(B_65))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'E'(s('0'),f(suc(suc(B_65))))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63))) ) ).

cnf(clause_6,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_80))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(B_80)))
    | ~ 'LE'(f(suc(C_32)),s('0'))
    | ~ 'E'(s('0'),f(B_80))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_80),f(suc(B_80)))
    | 'E'('0',f(suc(C_32)))
    | 'LE'(f(C_32),'0') ) ).

cnf(clause_223,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(C_22),s('0'))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'('0',f(C_22))
    | 'LE'(f(C_22),'0') ) ).

cnf(clause_971,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_26))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s('0'),f(B_26))
    | ~ 'E'(f(B_26),f(suc(B_26)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s('0'),f(suc(suc(B_26))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s('0'),f(suc(B_26))) ) ).

cnf(clause_714,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'('0',f(suc(suc(B_78))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_78),f(suc(B_78)))
    | ~ 'E'('0',f(B_78))
    | ~ 'E'('0',f(suc(B_78)))
    | ~ iLEQ(suc(B_75),suc(B_78))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_75),f(suc(B_75))) ) ).

cnf(clause_1070,axiom,
    ( ~ 'LE'(f(C_14),s(s(s(s('0')))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | 'E'(s(s(s('0'))),f(C_14))
    | 'LE'(f(C_14),s(s(s('0')))) ) ).

cnf(clause_388,axiom,
    ( ~ 'LE'(f(suc(C_21)),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(suc(C_21)))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_75,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'LE'(f(suc(C_20)),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'('0',f(suc(C_20)))
    | 'LE'(f(C_20),'0') ) ).

cnf(clause_147,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'LE'(f(suc(C_31)),s('0'))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(suc(C_31)))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_936,axiom,
    ( ~ 'E'(f(B_0),f(suc(B_0)))
    | ~ 'E'(f(B),f(suc(B)))
    | ~ iLEQ(suc(A_0),suc(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(B_0)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(B_0))))
    | ~ iLEQ(suc(B),suc(B_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(B_0))
    | 'E'(f(A_0),f(suc(A_0))) ) ).

cnf(clause_297,axiom,
    ( ~ 'LE'(f(suc(B_31)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B_31)))
    | 'LE'(f(B_31),s(s(s(s('0'))))) ) ).

cnf(clause_632,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_39))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_39)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_41))))
    | ~ 'E'(s(s(s('0'))),f(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_39),f(suc(B_39)))
    | ~ 'E'(f(B_41),f(suc(B_41)))
    | ~ iLEQ(suc(A_1),suc(B_39))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_41))
    | ~ 'E'(s(s('0')),f(suc(B_41)))
    | ~ iLEQ(suc(B_39),suc(B_41))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_420,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_63))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s('0')),f(B_63))
    | ~ 'LE'(f(C_27),s(s('0')))
    | ~ 'E'(s(s('0')),f(suc(B_63)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_63),f(suc(B_63)))
    | 'E'(s('0'),f(C_27))
    | 'LE'(f(C_27),s('0')) ) ).

cnf(clause_623,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_45)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_45))
    | ~ iLEQ(suc(A_1),suc(B_45))
    | ~ 'LE'(f(C_21),s(s('0')))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_45),f(suc(B_45)))
    | 'E'(s('0'),f(C_21))
    | 'LE'(f(C_21),s('0')) ) ).

cnf(clause_883,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'LE'(f(suc(suc(C_9))),s(s('0')))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ iLEQ(suc(A_0),suc(B_14))
    | ~ 'E'(s(s(s('0'))),f(B_14))
    | ~ 'E'(s(s(s('0'))),f(suc(B_14)))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_14),f(suc(B_14)))
    | 'E'(s('0'),f(suc(suc(C_9))))
    | 'LE'(f(C_9),s('0')) ) ).

cnf(clause_796,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(B_68),f(suc(B_68))) ) ).

cnf(clause_20,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'LE'(f(C_26),s('0'))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(f(B_57),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_57))))
    | 'E'('0',f(C_26))
    | 'LE'(f(C_26),'0') ) ).

cnf(clause_808,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'LE'(f(B_49),s(s('0')))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(s('0'),f(B_49))
    | 'LE'(f(B_49),s('0')) ) ).

cnf(clause_786,axiom,
    ( ~ 'E'(s('0'),f(B_68))
    | ~ 'E'('0',f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_70)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ 'E'('0',f(suc(suc(B_70))))
    | ~ iLEQ(suc(B_68),suc(B_70))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_249,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_57))
    | ~ 'E'(s(s(s('0'))),f(B_57))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ iLEQ(suc(B_57),suc(B_58))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_57)))
    | ~ 'E'(s(s(s('0'))),f(B_58))
    | ~ 'E'(s(s(s('0'))),f(suc(B_58)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_57),f(suc(B_57)))
    | 'E'(f(B_58),f(suc(B_58))) ) ).

cnf(clause_924,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(suc(A_0))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(f(A_0),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(B_25),f(suc(B_25)))
    | 'E'(f(B_27),f(suc(B_27))) ) ).

cnf(clause_1039,axiom,
    ( ~ 'E'('0',f(B_89))
    | ~ 'E'(f(B_89),f(suc(B_89)))
    | ~ 'E'('0',f(suc(B_89)))
    | ~ iLEQ(suc(B_87),suc(B_89))
    | ~ 'E'(s('0'),f(suc(suc(B_87))))
    | ~ 'E'(f(B_87),f(suc(B_87)))
    | ~ 'E'(s('0'),f(suc(B_87)))
    | ~ 'E'(s('0'),f(B_87))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ iLEQ(suc(A_4),suc(B_87))
    | ~ 'E'('0',f(suc(suc(B_89))))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_244,axiom,
    ( ~ 'E'(s('0'),f(B_69))
    | ~ 'E'(s('0'),f(B_68))
    | ~ 'E'(s('0'),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(B_69)))
    | ~ 'E'(s('0'),f(suc(suc(B_68))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_68))
    | ~ 'E'(f(B_68),f(suc(B_68)))
    | ~ iLEQ(suc(B_68),suc(B_69))
    | ~ 'E'(s('0'),f(suc(B_68)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_882,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_75)))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'LE'(f(C_31),s('0'))
    | ~ iLEQ(suc(A_3),suc(B_75))
    | ~ 'E'(s(s('0')),f(B_75))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_75),f(suc(B_75)))
    | 'E'('0',f(C_31))
    | 'LE'(f(C_31),'0') ) ).

cnf(clause_219,axiom,
    ( ~ iLEQ(suc(B_25),suc(B_27))
    | ~ iLEQ(suc(A_0),suc(B_25))
    | ~ 'E'('0',f(suc(B_27)))
    | ~ 'E'(s('0'),f(suc(B_25)))
    | ~ 'E'(s(s(s(s(s('0'))))),f(A_0))
    | ~ 'E'(s('0'),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s(s(s('0'))))),f(suc(A_0)))
    | ~ 'E'(s('0'),f(B_25))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'('0',f(B_27))
    | 'E'(f(A_0),f(suc(A_0)))
    | 'E'(f(B_27),f(suc(B_27))) ) ).

cnf(clause_818,axiom,
    ( ~ 'LE'(f(B_44),s(s(s('0'))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(s(s('0')),f(B_44))
    | 'LE'(f(B_44),s(s('0'))) ) ).

cnf(clause_543,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_32)))
    | ~ iLEQ(suc(A_1),suc(B_32))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(B_32))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_32),f(suc(B_32)))
    | iLEQ(suc(B_32),suc(B_32)) ) ).

%------------------------------------------------------------------------------
