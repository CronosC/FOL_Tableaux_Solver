%------------------------------------------------------------------------------
% File     : SYO658-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_1_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_1_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   34 (   2 unt;  20 nHn;  33 RR)
%            Number of literals    :  246 (   0 equ; 195 neg)
%            Maximal clause size   :   13 (   7 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   51 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_167,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6))) ) ).

cnf(clause_75,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_2)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_2)))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_104,axiom,
    ( ~ 'LE'(f(suc(B_2)),s(s('0')))
    | 'E'(s('0'),f(suc(B_2)))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_81,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_36,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_150,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_141,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s('0'))
    | 'E'('0',f(suc(suc(B_5))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_87,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_78,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_4,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_72,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_142,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_108,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_140,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_80,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_41,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_139,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_51,axiom,
    ( ~ 'LE'(f(B_2),s(s('0')))
    | 'E'(s('0'),f(B_2))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_71,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_30,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_151,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_5)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_5)))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_174,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_29,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_40,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_130,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_16,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_109,axiom,
    ( ~ 'LE'(f(B_5),s('0'))
    | 'E'('0',f(B_5))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_129,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_2))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_55,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_65,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_122,axiom,
    ( ~ 'LE'(f(suc(B_5)),s('0'))
    | 'E'('0',f(suc(B_5)))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_162,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_93,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_134,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

%------------------------------------------------------------------------------
