%------------------------------------------------------------------------------
% File     : SYO649-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_1_1_5
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_1_1_5 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   38 (   2 unt;  26 nHn;  37 RR)
%            Number of literals    :  424 (   0 equ; 362 neg)
%            Maximal clause size   :   21 (  11 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   62 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_252,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_2)))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1)))))) ) ).

cnf(clause_375,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_1480,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_703,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(suc(suc(suc(B_2)))))) ) ).

cnf(clause_1507,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_62,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(suc(B_1)))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(suc(B_1)))))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_716,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_999,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_512,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_774,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_771,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_962,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_1282,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_1501,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1012,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_1214,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_1)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_1)))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_365,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_1033,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_1))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_1))))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_1136,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_2)))))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_1172,axiom,
    ( ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1046,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_2))))))) ) ).

cnf(clause_258,axiom,
    ( ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_162,axiom,
    ( ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(suc(B_2)))) ) ).

cnf(clause_909,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_985,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_519,axiom,
    ( ~ 'LE'(f(suc(suc(B_1))),s('0'))
    | 'E'('0',f(suc(suc(B_1))))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_1121,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_2)))))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_1522,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(suc(suc(suc(B_2)))))) ) ).

cnf(clause_349,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(B_2))) ) ).

cnf(clause_369,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(B_2)))))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_412,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_2),f(suc(suc(suc(B_2))))) ) ).

cnf(clause_649,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'('0',f(suc(suc(suc(suc(suc(A_1)))))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(suc(suc(B_2)))))) ) ).

cnf(clause_314,axiom,
    ( ~ 'LE'(f(B_1),s('0'))
    | 'E'('0',f(B_1))
    | 'LE'(f(B_1),'0') ) ).

cnf(clause_102,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(A_1),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_2),f(suc(suc(suc(suc(B_2)))))) ) ).

cnf(clause_1514,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(A_1)))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1370,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(B_2),f(suc(suc(B_2))))
    | ~ 'E'('0',f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(A_1))))
    | ~ 'E'('0',f(A_1))
    | ~ 'E'('0',f(suc(B_2)))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_2))))))
    | ~ 'E'(f(B_2),f(suc(B_2)))
    | ~ iLEQ(suc(A_1),suc(B_2))
    | ~ 'E'('0',f(B_2))
    | ~ 'E'(f(B_2),f(suc(suc(suc(B_2)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'('0',f(suc(suc(B_2))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_2),f(suc(suc(suc(suc(B_2)))))) ) ).

cnf(clause_1382,axiom,
    'LE'(f(A),s('0')) ).

cnf(clause_1518,axiom,
    ( ~ 'LE'(f(suc(B_1)),s('0'))
    | 'E'('0',f(suc(B_1)))
    | 'LE'(f(B_1),'0') ) ).

%------------------------------------------------------------------------------
