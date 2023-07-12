%--------------------------------------------------------------------------
% File     : SYN649-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Syntactic
% Problem  : Harrison problem 4403
% Version  : Especial.
% English  :

% Refs     : [Har01] Email to G. Sutcliffe
% Source   : [Har01]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.25 v7.4.0, 0.17 v7.3.0, 0.25 v6.2.0, 0.33 v6.1.0, 0.14 v6.0.0, 0.11 v5.5.0, 0.12 v5.4.0, 0.17 v5.3.0, 0.20 v5.2.0, 0.23 v5.1.0, 0.19 v5.0.0, 0.20 v4.1.0, 0.13 v4.0.1, 0.14 v3.4.0, 0.20 v3.3.0, 0.33 v3.1.0, 0.17 v2.7.0, 0.00 v2.5.0
% Syntax   : Number of clauses     :   44 (  13 unt;   0 nHn;  31 RR)
%            Number of literals    :  100 (   0 equ;  57 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number of predicates  :   13 (  13 usr;   0 prp; 2-2 aty)
%            Number of functors    :   19 (  19 usr;  10 con; 0-2 aty)
%            Number of variables   :  115 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(p11_1,negated_conjecture,
    p11(X0,X0) ).

cnf(p9_2,negated_conjecture,
    p9(X80,X80) ).

cnf(p8_3,negated_conjecture,
    p8(X77,X77) ).

cnf(p6_4,negated_conjecture,
    p6(X70,X70) ).

cnf(p4_5,negated_conjecture,
    p4(X63,X63) ).

cnf(p3_6,negated_conjecture,
    p3(X56,X56) ).

cnf(p21_7,negated_conjecture,
    p21(X38,X38) ).

cnf(p2_8,negated_conjecture,
    p2(X31,X31) ).

cnf(p19_9,negated_conjecture,
    p19(X28,X28) ).

cnf(p17_10,negated_conjecture,
    p17(X21,X21) ).

cnf(p15_11,negated_conjecture,
    p15(X14,X14) ).

cnf(p13_12,negated_conjecture,
    p13(X3,X3) ).

cnf(p11_13,negated_conjecture,
    ( p11(X1,X2)
    | ~ p11(X0,X1)
    | ~ p11(X0,X2) ) ).

cnf(p9_14,negated_conjecture,
    ( p9(X81,X82)
    | ~ p9(X80,X81)
    | ~ p9(X80,X82) ) ).

cnf(p8_15,negated_conjecture,
    ( p8(X78,X79)
    | ~ p8(X77,X78)
    | ~ p8(X77,X79) ) ).

cnf(p6_16,negated_conjecture,
    ( p6(X71,X72)
    | ~ p6(X70,X71)
    | ~ p6(X70,X72) ) ).

cnf(p4_17,negated_conjecture,
    ( p4(X64,X65)
    | ~ p4(X63,X64)
    | ~ p4(X63,X65) ) ).

cnf(p3_18,negated_conjecture,
    ( p3(X57,X58)
    | ~ p3(X56,X57)
    | ~ p3(X56,X58) ) ).

cnf(p21_19,negated_conjecture,
    ( p21(X39,X40)
    | ~ p21(X38,X39)
    | ~ p21(X38,X40) ) ).

cnf(p2_20,negated_conjecture,
    ( p2(X32,X33)
    | ~ p2(X31,X32)
    | ~ p2(X31,X33) ) ).

cnf(p19_21,negated_conjecture,
    ( p19(X29,X30)
    | ~ p19(X28,X29)
    | ~ p19(X28,X30) ) ).

cnf(p17_22,negated_conjecture,
    ( p17(X22,X23)
    | ~ p17(X21,X22)
    | ~ p17(X21,X23) ) ).

cnf(p15_23,negated_conjecture,
    ( p15(X15,X16)
    | ~ p15(X14,X15)
    | ~ p15(X14,X16) ) ).

cnf(p13_24,negated_conjecture,
    ( p13(X4,X5)
    | ~ p13(X3,X4)
    | ~ p13(X3,X5) ) ).

cnf(p23_25,negated_conjecture,
    ( p23(X41,X42)
    | ~ p3(X44,X42)
    | ~ p4(X43,X41)
    | ~ p23(X43,X44) ) ).

cnf(p23_26,negated_conjecture,
    p23(f5(f7(f10(c26,f12(c27,f12(c27,c28))),c24),c25),c29) ).

cnf(p9_27,negated_conjecture,
    ( p9(f12(X83,X84),f12(X85,X86))
    | ~ p11(X83,X85)
    | ~ p9(X84,X86) ) ).

cnf(p13_28,negated_conjecture,
    ( p13(f16(X6,X7),f16(X8,X9))
    | ~ p15(X6,X8)
    | ~ p2(X7,X9) ) ).

cnf(p13_29,negated_conjecture,
    ( p13(f22(X10,X11),f22(X12,X13))
    | ~ p21(X10,X12)
    | ~ p3(X11,X13) ) ).

cnf(p15_30,negated_conjecture,
    ( p15(f18(X17,X18),f18(X19,X20))
    | ~ p17(X17,X19)
    | ~ p3(X18,X20) ) ).

cnf(p17_31,negated_conjecture,
    ( p17(f20(X24,X25),f20(X26,X27))
    | ~ p19(X24,X26)
    | ~ p9(X25,X27) ) ).

cnf(p2_32,negated_conjecture,
    ( p2(f7(X34,X35),f7(X36,X37))
    | ~ p2(X35,X37)
    | ~ p6(X34,X36) ) ).

cnf(p3_33,negated_conjecture,
    ( p3(f14(X59,X60),f14(X61,X62))
    | ~ p13(X59,X61)
    | ~ p3(X60,X62) ) ).

cnf(p4_34,negated_conjecture,
    ( p4(f5(X66,X67),f5(X68,X69))
    | ~ p2(X66,X68)
    | ~ p3(X67,X69) ) ).

cnf(p6_35,negated_conjecture,
    ( p6(f10(X73,X74),f10(X75,X76))
    | ~ p8(X73,X75)
    | ~ p9(X74,X76) ) ).

cnf(p3_36,negated_conjecture,
    ( p3(X54,X55)
    | ~ p23(f5(f7(f10(c26,f12(c31,c32)),X53),X54),X55) ) ).

cnf(p23_37,negated_conjecture,
    ( p23(f5(f7(f10(c26,f12(c31,c32)),X53),X54),X55)
    | ~ p3(X54,X55) ) ).

cnf(not_p23_38,negated_conjecture,
    ( ~ p23(f5(c24,c25),X87)
    | ~ p23(f5(f7(f10(c26,f12(c27,c28)),c24),X87),c29) ) ).

cnf(p23_39,negated_conjecture,
    ( p23(f5(c24,X49),f14(f22(c33,X50),X49))
    | ~ p23(f5(f7(f10(c26,f12(c27,c28)),c24),X49),X50) ) ).

cnf(p23_40,negated_conjecture,
    ( p23(f5(X45,f14(f16(f18(f20(c30,X46),X47),X45),X48)),X48)
    | ~ p23(f5(f7(f10(c26,f12(c27,X46)),X45),X47),X48) ) ).

cnf(p23_41,negated_conjecture,
    ( p23(f5(f7(f10(c26,c28),c24),f14(f22(c33,X50),X49)),X50)
    | ~ p23(f5(f7(f10(c26,f12(c27,c28)),c24),X49),X50) ) ).

cnf(p23_42,negated_conjecture,
    ( p23(f5(f7(f10(c26,f12(c27,X46)),X45),X47),X48)
    | ~ p23(f5(X45,X51),X48)
    | ~ p23(f5(f7(f10(c26,X46),X45),X47),X51) ) ).

cnf(p23_43,negated_conjecture,
    ( p23(f5(f7(f10(c26,f12(c27,c28)),c24),X49),X50)
    | ~ p23(f5(c24,X49),X52)
    | ~ p23(f5(f7(f10(c26,c28),c24),X52),X50) ) ).

cnf(p23_44,negated_conjecture,
    ( p23(f5(f7(f10(c26,X46),X45),X47),f14(f16(f18(f20(c30,X46),X47),X45),X48))
    | ~ p23(f5(f7(f10(c26,f12(c27,X46)),X45),X47),X48) ) ).

%--------------------------------------------------------------------------