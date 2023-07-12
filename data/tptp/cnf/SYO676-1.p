%------------------------------------------------------------------------------
% File     : SYO676-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_0_5
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_0_5 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   46 (   2 unt;  24 nHn;  45 RR)
%            Number of literals    :  210 (   0 equ; 145 neg)
%            Maximal clause size   :   10 (   4 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   45 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_29,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

cnf(clause_31,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_16,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B))))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B))))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_84,axiom,
    ( ~ 'LE'(f(suc(B_1)),s(s('0')))
    | 'E'(s('0'),f(suc(B_1)))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_35,axiom,
    ( ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1)))))) ) ).

cnf(clause_74,axiom,
    ( ~ 'LE'(f(suc(B_2)),s('0'))
    | 'E'('0',f(suc(B_2)))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_100,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_130,axiom,
    ( ~ 'E'(f(A_4),f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_4)))))))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_52,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_87,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_2)))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(suc(B_2)))))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_27,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B)))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_11,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_85,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_38,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4))))) ) ).

cnf(clause_3,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_0)))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(suc(B_0)))))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_63,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_2)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_2)))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_50,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_104,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_1)))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(suc(B_1)))))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_22,axiom,
    ( ~ 'LE'(f(B_2),s('0'))
    | 'E'('0',f(B_2))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_121,axiom,
    ( ~ 'LE'(f(B),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_64,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_10,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(suc(A_4)))))) ) ).

cnf(clause_42,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2)))))) ) ).

cnf(clause_56,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_1)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_1)))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_45,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_95,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_0))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(B_0))))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_4,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B)))))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(suc(suc(B)))))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_128,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s('0'))
    | 'E'('0',f(suc(suc(B_2))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_62,axiom,
    ( ~ 'LE'(f(suc(B_0)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_0)))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_96,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(A_3),f(suc(suc(suc(suc(A_3)))))) ) ).

cnf(clause_91,axiom,
    ( ~ 'LE'(f(suc(suc(B_1))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_1))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_41,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_3)))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(suc(A_3)))) ) ).

cnf(clause_40,axiom,
    ( ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1)))))) ) ).

cnf(clause_20,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_2))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_81,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_6,axiom,
    ( ~ 'LE'(f(suc(suc(B))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_102,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_46,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_0)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_0)))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_125,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_1))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_1))))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_109,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_86,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_105,axiom,
    ( ~ 'LE'(f(suc(B)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B)))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_58,axiom,
    ( ~ 'LE'(f(B_1),s(s('0')))
    | 'E'(s('0'),f(B_1))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_98,axiom,
    ( ~ 'LE'(f(B_0),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_0))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_60,axiom,
    ( ~ 'LE'(f(suc(suc(B_0))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_0))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_8,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

%------------------------------------------------------------------------------
