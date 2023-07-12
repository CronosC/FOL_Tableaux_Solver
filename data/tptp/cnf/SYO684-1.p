%------------------------------------------------------------------------------
% File     : SYO684-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_0_4
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_0_4 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   47 (   2 unt;  25 nHn;  46 RR)
%            Number of literals    :  192 (   0 equ; 126 neg)
%            Maximal clause size   :    8 (   4 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   46 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_29,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3)) ) ).

cnf(clause_26,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_60,axiom,
    ( ~ 'LE'(f(suc(B_0)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_0)))
    | 'LE'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_70,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B)))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(suc(B)))))
    | 'LE'(f(B),s(s(s(s('0'))))) ) ).

cnf(clause_41,axiom,
    ( ~ 'LE'(f(suc(B_1)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_1)))
    | 'LE'(f(B_1),s(s('0'))) ) ).

cnf(clause_34,axiom,
    ( ~ 'LE'(f(B_0),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_0))
    | 'LE'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_30,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_2,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_0))))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_0))))))
    | 'LE'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_27,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4)))))) ) ).

cnf(clause_35,axiom,
    ( ~ 'LE'(f(suc(suc(B))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B))))
    | 'LE'(f(B),s(s(s(s('0'))))) ) ).

cnf(clause_40,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_46,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_39,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_3)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_3)))))
    | 'LE'(f(B_3),'0') ) ).

cnf(clause_47,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_1)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_1)))))
    | 'LE'(f(B_1),s(s('0'))) ) ).

cnf(clause_15,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_71,axiom,
    ( ~ 'LE'(f(suc(suc(B_0))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_0))))
    | 'LE'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_36,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_3))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_3))))))
    | 'LE'(f(B_3),'0') ) ).

cnf(clause_31,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_55,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_51,axiom,
    ( ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(A_5))
    | 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_66,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_1))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(B_1))))))
    | 'LE'(f(B_1),s(s('0'))) ) ).

cnf(clause_8,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_67,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_4,axiom,
    ( ~ 'LE'(f(suc(B)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B)))
    | 'LE'(f(B),s(s(s(s('0'))))) ) ).

cnf(clause_10,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4))))) ) ).

cnf(clause_56,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_42,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_9,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_80,axiom,
    ( ~ 'LE'(f(suc(suc(B_1))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_1))))
    | 'LE'(f(B_1),s(s('0'))) ) ).

cnf(clause_22,axiom,
    ( ~ 'LE'(f(B_2),s(s('0')))
    | 'E'(s('0'),f(B_2))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_44,axiom,
    ( ~ 'LE'(f(B_1),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_1))
    | 'LE'(f(B_1),s(s('0'))) ) ).

cnf(clause_24,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_0)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B_0)))))
    | 'LE'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_3,axiom,
    ( ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1)) ) ).

cnf(clause_79,axiom,
    ( ~ 'LE'(f(B),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B))
    | 'LE'(f(B),s(s(s(s('0'))))) ) ).

cnf(clause_19,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_25,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_57,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_2))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_68,axiom,
    ( ~ 'LE'(f(suc(suc(B_3))),s('0'))
    | 'E'('0',f(suc(suc(B_3))))
    | 'LE'(f(B_3),'0') ) ).

cnf(clause_7,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_2))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_2))))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_21,axiom,
    ( ~ 'LE'(f(suc(B_3)),s('0'))
    | 'E'('0',f(suc(B_3)))
    | 'LE'(f(B_3),'0') ) ).

cnf(clause_32,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_2)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_2)))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_50,axiom,
    ( ~ 'LE'(f(suc(B_2)),s(s('0')))
    | 'E'(s('0'),f(suc(B_2)))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_62,axiom,
    ( ~ 'LE'(f(B_3),s('0'))
    | 'E'('0',f(B_3))
    | 'LE'(f(B_3),'0') ) ).

cnf(clause_69,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B))))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B))))))
    | 'LE'(f(B),s(s(s(s('0'))))) ) ).

cnf(clause_76,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_72,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(A_5),f(suc(suc(suc(A_5))))) ) ).

cnf(clause_14,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

%------------------------------------------------------------------------------
