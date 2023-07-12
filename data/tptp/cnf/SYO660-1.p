%------------------------------------------------------------------------------
% File     : SYO660-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_1_5
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_1_5 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   74 (   2 unt;  52 nHn;  73 RR)
%            Number of literals    :  846 (   0 equ; 723 neg)
%            Maximal clause size   :   21 (  11 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  123 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_1847,axiom,
    ( ~ 'LE'(f(suc(B_2)),s(s('0')))
    | 'E'(s('0'),f(suc(B_2)))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_794,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(suc(suc(B_3))))) ) ).

cnf(clause_1502,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_1962,axiom,
    ( ~ 'LE'(f(B_5),s('0'))
    | 'E'('0',f(B_5))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_2540,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s('0'))
    | 'E'('0',f(suc(suc(B_5))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_1397,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2034,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(B_3)))))))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_2529,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(B_3),f(suc(suc(suc(B_3))))) ) ).

cnf(clause_467,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(suc(suc(suc(B_6)))))) ) ).

cnf(clause_2680,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_2600,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_2932,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2724,axiom,
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
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_169,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_572,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_623,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_147,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_6)))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_2543,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_6),f(suc(suc(suc(suc(B_6)))))) ) ).

cnf(clause_1826,axiom,
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
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_1946,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(suc(suc(B_6)))))) ) ).

cnf(clause_724,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_3),f(suc(suc(suc(suc(B_3)))))) ) ).

cnf(clause_2580,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(suc(suc(suc(B_3)))))) ) ).

cnf(clause_2384,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(B_3)))))))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1)))))) ) ).

cnf(clause_2165,axiom,
    ( ~ 'LE'(f(suc(B_5)),s('0'))
    | 'E'('0',f(suc(B_5)))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_1707,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_6)))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_3037,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_733,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_6)))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_2700,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_5)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_5)))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_1276,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_2)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_2)))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_1696,axiom,
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
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_3),f(suc(suc(suc(B_3))))) ) ).

cnf(clause_1388,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_1114,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_1574,axiom,
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
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_2118,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_6),f(suc(suc(suc(suc(B_6)))))) ) ).

cnf(clause_410,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_2))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_2))))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_1151,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | 'E'(f(B_6),f(suc(suc(suc(suc(B_6)))))) ) ).

cnf(clause_669,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_1225,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_3),f(suc(suc(suc(B_3))))) ) ).

cnf(clause_664,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2336,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_2))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_70,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_514,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_5))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_5))))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_2196,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1410,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(suc(suc(suc(B_3)))))) ) ).

cnf(clause_1927,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_3120,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_1896,axiom,
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
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_2649,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(B_3)))))))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_165,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_6)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6))) ) ).

cnf(clause_842,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_344,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(B_3)))))))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_2349,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_997,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_249,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_2)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2494,axiom,
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
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(suc(suc(B_3))))) ) ).

cnf(clause_1158,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(B_3)))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1595,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_2)))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(suc(B_2)))))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_1195,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_6)))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'('0',f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(suc(suc(suc(A_2)))))) ) ).

cnf(clause_1204,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_5)))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(suc(B_5)))))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_1186,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_934,axiom,
    ( ~ 'LE'(f(B_2),s(s('0')))
    | 'E'(s('0'),f(B_2))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_1137,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_1944,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_2717,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_3),f(suc(suc(suc(suc(B_3)))))) ) ).

cnf(clause_2795,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_692,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_3),f(suc(suc(B_3)))) ) ).

cnf(clause_2550,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_1325,axiom,
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

cnf(clause_720,axiom,
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

cnf(clause_1634,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_307,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2827,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_3))))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_3)))))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_3),f(suc(suc(suc(B_3)))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_3),f(suc(suc(B_3))))
    | 'E'(f(B_3),f(suc(suc(suc(suc(B_3)))))) ) ).

cnf(clause_1215,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_2367,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

%------------------------------------------------------------------------------
