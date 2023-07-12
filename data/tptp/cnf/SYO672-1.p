%------------------------------------------------------------------------------
% File     : SYO672-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_2_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_2_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :  104 (   2 unt;  78 nHn; 103 RR)
%            Number of literals    : 1385 (   0 equ;1183 neg)
%            Maximal clause size   :   20 (  13 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  265 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_2291,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_112,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_607,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_1628,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_1935,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_1132,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1427,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_1512,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_1108,axiom,
    ( ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_786,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_230,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(suc(B_29)))) ) ).

cnf(clause_610,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_275,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_78,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_2162,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_488,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_441,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_2324,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_1424,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_1978,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_29),f(suc(suc(B_29)))) ) ).

cnf(clause_490,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_125,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_1546,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_802,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_2052,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_1175,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_16))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_788,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_2166,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_939,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_2285,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_22,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_333,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_2357,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_2191,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_831,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_839,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_1449,axiom,
    ( ~ 'LE'(f(B_16),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_16))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_1916,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_889,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_1465,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_1841,axiom,
    ( ~ 'LE'(f(B_28),s(s('0')))
    | 'E'(s('0'),f(B_28))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_246,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_117,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_94,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_1986,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_921,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_16)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_16)))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_299,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30)))) ) ).

cnf(clause_1301,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_1187,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_994,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_35)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_35)))))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_959,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_362,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_691,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(suc(B_36)))) ) ).

cnf(clause_1140,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_1637,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_1230,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_109,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(suc(B_36)))) ) ).

cnf(clause_1941,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_101,axiom,
    ( ~ 'LE'(f(suc(suc(B_28))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_28))))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_848,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37)) ) ).

cnf(clause_77,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(suc(B_29)))) ) ).

cnf(clause_1761,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1223,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_1277,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_1160,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_415,axiom,
    ( ~ 'LE'(f(suc(suc(B_35))),s('0'))
    | 'E'('0',f(suc(suc(B_35))))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_838,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_528,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_2026,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_712,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_465,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_2086,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17)))) ) ).

cnf(clause_593,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2247,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_85,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_1173,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_1579,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1642,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_28)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_28)))))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_66,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1933,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(suc(B_36)))) ) ).

cnf(clause_1307,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_298,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_604,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1610,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_783,axiom,
    ( ~ 'LE'(f(suc(B_28)),s(s('0')))
    | 'E'(s('0'),f(suc(B_28)))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_56,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_1857,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_976,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_1338,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_2008,axiom,
    ( ~ 'LE'(f(suc(B_35)),s('0'))
    | 'E'('0',f(suc(B_35)))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_179,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2366,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_669,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(suc(B_30)))) ) ).

cnf(clause_50,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_18)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_2017,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_17),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_717,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_36),f(suc(suc(B_36))))
    | 'E'(f(B_37),f(suc(suc(B_37)))) ) ).

cnf(clause_2215,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_778,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_2111,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1197,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(suc(B_29))))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_1030,axiom,
    ( ~ 'LE'(f(suc(B_16)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_16)))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_2364,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(suc(B_29)))))
    | ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(suc(B_30))))
    | ~ 'E'(f(B_29),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_30)))))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_1753,axiom,
    ( ~ 'LE'(f(B_35),s('0'))
    | 'E'('0',f(B_35))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_199,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'(f(B_37),f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(suc(suc(B_37)))))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ 'E'('0',f(suc(suc(suc(B_36)))))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

%------------------------------------------------------------------------------
