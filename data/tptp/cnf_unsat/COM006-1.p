%--------------------------------------------------------------------------
% File     : COM006-1 : TPTP v8.1.2. Released v2.7.0.
% Domain   : Computing Theory
% Problem  : Behaviour of an algorithm that orients rings with 5 nodes
% Version  : Especial.
% English  :

% Refs     : [Hoe94] Hoepman (1994), Uniform Deterministic Self-Stabilizing
%          : [Kon03] Konev (2003), Email to G. Sutcliffe
% Source   : [Kon03]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.57 v8.1.0, 0.43 v7.5.0, 0.33 v7.4.0, 0.67 v7.2.0, 0.83 v7.1.0, 0.67 v7.0.0, 0.75 v6.4.0, 0.62 v6.3.0, 0.71 v6.2.0, 0.89 v6.1.0, 1.00 v6.0.0, 0.86 v5.5.0, 0.88 v5.4.0, 0.90 v5.1.0, 0.91 v5.0.0, 0.93 v4.1.0, 0.88 v4.0.1, 0.80 v4.0.0, 0.86 v3.4.0, 1.00 v3.3.0, 0.67 v3.1.0, 1.00 v2.7.0
% Syntax   : Number of clauses     :  449 (   1 unt; 262 nHn; 447 RR)
%            Number of literals    : 2286 (   0 equ;1310 neg)
%            Maximal clause size   :    8 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   40 (  40 usr;   0 prp; 1-1 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :  448 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(c001,negated_conjecture,
    ap(a) ).

cnf(c002,negated_conjecture,
    ( ~ ap(X)
    | ~ aq(X) ) ).

cnf(c003,negated_conjecture,
    ( ~ ap(X)
    | ~ ar(X) ) ).

cnf(c004,negated_conjecture,
    ( ~ ap(X)
    | ~ as(X) ) ).

cnf(c005,negated_conjecture,
    ( ~ ap(X)
    | ~ at(X) ) ).

cnf(c006,negated_conjecture,
    ( ~ aq(X)
    | ~ ar(X) ) ).

cnf(c007,negated_conjecture,
    ( ~ aq(X)
    | ~ as(X) ) ).

cnf(c008,negated_conjecture,
    ( ~ aq(X)
    | ~ at(X) ) ).

cnf(c009,negated_conjecture,
    ( ~ ar(X)
    | ~ as(X) ) ).

cnf(c010,negated_conjecture,
    ( ~ ar(X)
    | ~ at(X) ) ).

cnf(c011,negated_conjecture,
    ( ~ as(X)
    | ~ at(X) ) ).

cnf(c012,negated_conjecture,
    ( ap(X)
    | aq(X)
    | ar(X)
    | as(X)
    | at(X) ) ).

cnf(c013,negated_conjecture,
    ( ~ pqr1(X)
    | ~ p(X) ) ).

cnf(c014,negated_conjecture,
    ( ~ pqr1(X)
    | pp(X) ) ).

cnf(c015,negated_conjecture,
    ( ~ pqr1(X)
    | ~ q(X) ) ).

cnf(c016,negated_conjecture,
    ( ~ pqr1(X)
    | ~ qq(X) ) ).

cnf(c017,negated_conjecture,
    ( ~ pqr1(X)
    | r(X) ) ).

cnf(c018,negated_conjecture,
    ( ~ pqr1(X)
    | ~ rr(X) ) ).

cnf(c019,negated_conjecture,
    ( ~ pqr1(X)
    | aq(X) ) ).

cnf(c020,negated_conjecture,
    ( ~ pqr2(X)
    | p(X) ) ).

cnf(c021,negated_conjecture,
    ( ~ pqr2(X)
    | pp(X) ) ).

cnf(c022,negated_conjecture,
    ( ~ pqr2(X)
    | q(X) ) ).

cnf(c023,negated_conjecture,
    ( ~ pqr2(X)
    | ~ qq(X) ) ).

cnf(c024,negated_conjecture,
    ( ~ pqr2(X)
    | ~ r(X) ) ).

cnf(c025,negated_conjecture,
    ( ~ pqr2(X)
    | ~ rr(X) ) ).

cnf(c026,negated_conjecture,
    ( ~ pqr2(X)
    | aq(X) ) ).

cnf(c027,negated_conjecture,
    ( ~ pqr3(X)
    | p(X) ) ).

cnf(c028,negated_conjecture,
    ( ~ pqr3(X)
    | ~ pp(X) ) ).

cnf(c029,negated_conjecture,
    ( ~ pqr3(X)
    | ~ q(X) ) ).

cnf(c030,negated_conjecture,
    ( ~ pqr3(X)
    | ~ qq(X) ) ).

cnf(c031,negated_conjecture,
    ( ~ pqr3(X)
    | ~ r(X) ) ).

cnf(c032,negated_conjecture,
    ( ~ pqr3(X)
    | rr(X) ) ).

cnf(c033,negated_conjecture,
    ( ~ pqr3(X)
    | aq(X) ) ).

cnf(c034,negated_conjecture,
    ( ~ pqr4(X)
    | ~ p(X) ) ).

cnf(c035,negated_conjecture,
    ( ~ pqr4(X)
    | ~ pp(X) ) ).

cnf(c036,negated_conjecture,
    ( ~ pqr4(X)
    | q(X) ) ).

cnf(c037,negated_conjecture,
    ( ~ pqr4(X)
    | ~ qq(X) ) ).

cnf(c038,negated_conjecture,
    ( ~ pqr4(X)
    | r(X) ) ).

cnf(c039,negated_conjecture,
    ( ~ pqr4(X)
    | rr(X) ) ).

cnf(c040,negated_conjecture,
    ( ~ pqr4(X)
    | aq(X) ) ).

cnf(c041,negated_conjecture,
    ( ~ qrs1(X)
    | ~ q(X) ) ).

cnf(c042,negated_conjecture,
    ( ~ qrs1(X)
    | qq(X) ) ).

cnf(c043,negated_conjecture,
    ( ~ qrs1(X)
    | ~ r(X) ) ).

cnf(c044,negated_conjecture,
    ( ~ qrs1(X)
    | ~ rr(X) ) ).

cnf(c045,negated_conjecture,
    ( ~ qrs1(X)
    | s(X) ) ).

cnf(c046,negated_conjecture,
    ( ~ qrs1(X)
    | ~ ss(X) ) ).

cnf(c047,negated_conjecture,
    ( ~ qrs1(X)
    | ar(X) ) ).

cnf(c048,negated_conjecture,
    ( ~ qrs2(X)
    | q(X) ) ).

cnf(c049,negated_conjecture,
    ( ~ qrs2(X)
    | qq(X) ) ).

cnf(c050,negated_conjecture,
    ( ~ qrs2(X)
    | r(X) ) ).

cnf(c051,negated_conjecture,
    ( ~ qrs2(X)
    | ~ rr(X) ) ).

cnf(c052,negated_conjecture,
    ( ~ qrs2(X)
    | ~ s(X) ) ).

cnf(c053,negated_conjecture,
    ( ~ qrs2(X)
    | ~ ss(X) ) ).

cnf(c054,negated_conjecture,
    ( ~ qrs2(X)
    | ar(X) ) ).

cnf(c055,negated_conjecture,
    ( ~ qrs3(X)
    | q(X) ) ).

cnf(c056,negated_conjecture,
    ( ~ qrs3(X)
    | ~ qq(X) ) ).

cnf(c057,negated_conjecture,
    ( ~ qrs3(X)
    | ~ r(X) ) ).

cnf(c058,negated_conjecture,
    ( ~ qrs3(X)
    | ~ rr(X) ) ).

cnf(c059,negated_conjecture,
    ( ~ qrs3(X)
    | ~ s(X) ) ).

cnf(c060,negated_conjecture,
    ( ~ qrs3(X)
    | ss(X) ) ).

cnf(c061,negated_conjecture,
    ( ~ qrs3(X)
    | ar(X) ) ).

cnf(c062,negated_conjecture,
    ( ~ qrs4(X)
    | ~ q(X) ) ).

cnf(c063,negated_conjecture,
    ( ~ qrs4(X)
    | ~ qq(X) ) ).

cnf(c064,negated_conjecture,
    ( ~ qrs4(X)
    | r(X) ) ).

cnf(c065,negated_conjecture,
    ( ~ qrs4(X)
    | ~ rr(X) ) ).

cnf(c066,negated_conjecture,
    ( ~ qrs4(X)
    | s(X) ) ).

cnf(c067,negated_conjecture,
    ( ~ qrs4(X)
    | ss(X) ) ).

cnf(c068,negated_conjecture,
    ( ~ qrs4(X)
    | ar(X) ) ).

cnf(c069,negated_conjecture,
    ( ~ rst1(X)
    | ~ r(X) ) ).

cnf(c070,negated_conjecture,
    ( ~ rst1(X)
    | rr(X) ) ).

cnf(c071,negated_conjecture,
    ( ~ rst1(X)
    | ~ s(X) ) ).

cnf(c072,negated_conjecture,
    ( ~ rst1(X)
    | ~ ss(X) ) ).

cnf(c073,negated_conjecture,
    ( ~ rst1(X)
    | t(X) ) ).

cnf(c074,negated_conjecture,
    ( ~ rst1(X)
    | ~ tt(X) ) ).

cnf(c075,negated_conjecture,
    ( ~ rst1(X)
    | as(X) ) ).

cnf(c076,negated_conjecture,
    ( ~ rst2(X)
    | r(X) ) ).

cnf(c077,negated_conjecture,
    ( ~ rst2(X)
    | rr(X) ) ).

cnf(c078,negated_conjecture,
    ( ~ rst2(X)
    | s(X) ) ).

cnf(c079,negated_conjecture,
    ( ~ rst2(X)
    | ~ ss(X) ) ).

cnf(c080,negated_conjecture,
    ( ~ rst2(X)
    | ~ t(X) ) ).

cnf(c081,negated_conjecture,
    ( ~ rst2(X)
    | ~ tt(X) ) ).

cnf(c082,negated_conjecture,
    ( ~ rst2(X)
    | as(X) ) ).

cnf(c083,negated_conjecture,
    ( ~ rst3(X)
    | r(X) ) ).

cnf(c084,negated_conjecture,
    ( ~ rst3(X)
    | ~ rr(X) ) ).

cnf(c085,negated_conjecture,
    ( ~ rst3(X)
    | ~ s(X) ) ).

cnf(c086,negated_conjecture,
    ( ~ rst3(X)
    | ~ ss(X) ) ).

cnf(c087,negated_conjecture,
    ( ~ rst3(X)
    | ~ t(X) ) ).

cnf(c088,negated_conjecture,
    ( ~ rst3(X)
    | tt(X) ) ).

cnf(c089,negated_conjecture,
    ( ~ rst3(X)
    | as(X) ) ).

cnf(c090,negated_conjecture,
    ( ~ rst4(X)
    | ~ r(X) ) ).

cnf(c091,negated_conjecture,
    ( ~ rst4(X)
    | ~ rr(X) ) ).

cnf(c092,negated_conjecture,
    ( ~ rst4(X)
    | s(X) ) ).

cnf(c093,negated_conjecture,
    ( ~ rst4(X)
    | ~ ss(X) ) ).

cnf(c094,negated_conjecture,
    ( ~ rst4(X)
    | t(X) ) ).

cnf(c095,negated_conjecture,
    ( ~ rst4(X)
    | tt(X) ) ).

cnf(c096,negated_conjecture,
    ( ~ rst4(X)
    | as(X) ) ).

cnf(c097,negated_conjecture,
    ( ~ stp1(X)
    | ~ s(X) ) ).

cnf(c098,negated_conjecture,
    ( ~ stp1(X)
    | ss(X) ) ).

cnf(c099,negated_conjecture,
    ( ~ stp1(X)
    | ~ t(X) ) ).

cnf(c100,negated_conjecture,
    ( ~ stp1(X)
    | ~ tt(X) ) ).

cnf(c101,negated_conjecture,
    ( ~ stp1(X)
    | p(X) ) ).

cnf(c102,negated_conjecture,
    ( ~ stp1(X)
    | ~ pp(X) ) ).

cnf(c103,negated_conjecture,
    ( ~ stp1(X)
    | at(X) ) ).

cnf(c104,negated_conjecture,
    ( ~ stp2(X)
    | s(X) ) ).

cnf(c105,negated_conjecture,
    ( ~ stp2(X)
    | ss(X) ) ).

cnf(c106,negated_conjecture,
    ( ~ stp2(X)
    | t(X) ) ).

cnf(c107,negated_conjecture,
    ( ~ stp2(X)
    | ~ tt(X) ) ).

cnf(c108,negated_conjecture,
    ( ~ stp2(X)
    | ~ p(X) ) ).

cnf(c109,negated_conjecture,
    ( ~ stp2(X)
    | ~ pp(X) ) ).

cnf(c110,negated_conjecture,
    ( ~ stp2(X)
    | at(X) ) ).

cnf(c111,negated_conjecture,
    ( ~ stp3(X)
    | s(X) ) ).

cnf(c112,negated_conjecture,
    ( ~ stp3(X)
    | ~ ss(X) ) ).

cnf(c113,negated_conjecture,
    ( ~ stp3(X)
    | ~ t(X) ) ).

cnf(c114,negated_conjecture,
    ( ~ stp3(X)
    | ~ tt(X) ) ).

cnf(c115,negated_conjecture,
    ( ~ stp3(X)
    | ~ p(X) ) ).

cnf(c116,negated_conjecture,
    ( ~ stp3(X)
    | pp(X) ) ).

cnf(c117,negated_conjecture,
    ( ~ stp3(X)
    | at(X) ) ).

cnf(c118,negated_conjecture,
    ( ~ stp4(X)
    | ~ s(X) ) ).

cnf(c119,negated_conjecture,
    ( ~ stp4(X)
    | ~ ss(X) ) ).

cnf(c120,negated_conjecture,
    ( ~ stp4(X)
    | t(X) ) ).

cnf(c121,negated_conjecture,
    ( ~ stp4(X)
    | ~ tt(X) ) ).

cnf(c122,negated_conjecture,
    ( ~ stp4(X)
    | p(X) ) ).

cnf(c123,negated_conjecture,
    ( ~ stp4(X)
    | pp(X) ) ).

cnf(c124,negated_conjecture,
    ( ~ stp4(X)
    | at(X) ) ).

cnf(c125,negated_conjecture,
    ( ~ tpq1(X)
    | ~ t(X) ) ).

cnf(c126,negated_conjecture,
    ( ~ tpq1(X)
    | tt(X) ) ).

cnf(c127,negated_conjecture,
    ( ~ tpq1(X)
    | ~ p(X) ) ).

cnf(c128,negated_conjecture,
    ( ~ tpq1(X)
    | ~ pp(X) ) ).

cnf(c129,negated_conjecture,
    ( ~ tpq1(X)
    | q(X) ) ).

cnf(c130,negated_conjecture,
    ( ~ tpq1(X)
    | ~ qq(X) ) ).

cnf(c131,negated_conjecture,
    ( ~ tpq1(X)
    | ap(X) ) ).

cnf(c132,negated_conjecture,
    ( ~ tpq2(X)
    | t(X) ) ).

cnf(c133,negated_conjecture,
    ( ~ tpq2(X)
    | tt(X) ) ).

cnf(c134,negated_conjecture,
    ( ~ tpq2(X)
    | p(X) ) ).

cnf(c135,negated_conjecture,
    ( ~ tpq2(X)
    | ~ pp(X) ) ).

cnf(c136,negated_conjecture,
    ( ~ tpq2(X)
    | ~ q(X) ) ).

cnf(c137,negated_conjecture,
    ( ~ tpq2(X)
    | ~ qq(X) ) ).

cnf(c138,negated_conjecture,
    ( ~ tpq2(X)
    | ap(X) ) ).

cnf(c139,negated_conjecture,
    ( ~ tpq3(X)
    | t(X) ) ).

cnf(c140,negated_conjecture,
    ( ~ tpq3(X)
    | ~ tt(X) ) ).

cnf(c141,negated_conjecture,
    ( ~ tpq3(X)
    | ~ p(X) ) ).

cnf(c142,negated_conjecture,
    ( ~ tpq3(X)
    | ~ pp(X) ) ).

cnf(c143,negated_conjecture,
    ( ~ tpq3(X)
    | ~ q(X) ) ).

cnf(c144,negated_conjecture,
    ( ~ tpq3(X)
    | qq(X) ) ).

cnf(c145,negated_conjecture,
    ( ~ tpq3(X)
    | ap(X) ) ).

cnf(c146,negated_conjecture,
    ( ~ tpq4(X)
    | ~ t(X) ) ).

cnf(c147,negated_conjecture,
    ( ~ tpq4(X)
    | ~ tt(X) ) ).

cnf(c148,negated_conjecture,
    ( ~ tpq4(X)
    | p(X) ) ).

cnf(c149,negated_conjecture,
    ( ~ tpq4(X)
    | ~ pp(X) ) ).

cnf(c150,negated_conjecture,
    ( ~ tpq4(X)
    | q(X) ) ).

cnf(c151,negated_conjecture,
    ( ~ tpq4(X)
    | qq(X) ) ).

cnf(c152,negated_conjecture,
    ( ~ tpq4(X)
    | ap(X) ) ).

cnf(c153,negated_conjecture,
    ( ~ tq(X)
    | ~ pr(X)
    | ~ qs(X)
    | ~ rt(X)
    | ~ sp(X) ) ).

cnf(c154,negated_conjecture,
    ( tq(X)
    | pr(X)
    | qs(X)
    | rt(X)
    | sp(X) ) ).

cnf(c155,negated_conjecture,
    ( ~ ap(X)
    | aq(f(X)) ) ).

cnf(c156,negated_conjecture,
    ( ~ aq(X)
    | ar(f(X)) ) ).

cnf(c157,negated_conjecture,
    ( ~ ar(X)
    | as(f(X)) ) ).

cnf(c158,negated_conjecture,
    ( ~ as(X)
    | at(f(X)) ) ).

cnf(c159,negated_conjecture,
    ( ~ at(X)
    | ap(f(X)) ) ).

cnf(c160,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | q(X)
    | r(X)
    | q(f(X)) ) ).

cnf(c161,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | q(X)
    | r(X)
    | ~ qq(f(X)) ) ).

cnf(c162,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | r(X)
    | q(f(X)) ) ).

cnf(c163,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | r(X)
    | ~ qq(f(X)) ) ).

cnf(c164,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ q(X)
    | ~ r(X)
    | ~ q(f(X)) ) ).

cnf(c165,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ q(X)
    | ~ r(X)
    | ~ qq(f(X)) ) ).

cnf(c166,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ r(X)
    | ~ q(f(X)) ) ).

cnf(c167,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ r(X)
    | ~ qq(f(X)) ) ).

cnf(c168,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | ~ q(f(X)) ) ).

cnf(c169,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | qq(f(X)) ) ).

cnf(c170,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ q(f(X)) ) ).

cnf(c171,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ qq(f(X)) ) ).

cnf(c172,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | q(f(X)) ) ).

cnf(c173,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | qq(f(X)) ) ).

cnf(c174,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | q(f(X)) ) ).

cnf(c175,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | ~ qq(f(X)) ) ).

cnf(c176,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | ~ q(f(X)) ) ).

cnf(c177,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c178,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | ~ rr(X)
    | ~ q(f(X)) ) ).

cnf(c179,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c180,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | q(f(X)) ) ).

cnf(c181,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c182,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ rr(X)
    | q(f(X)) ) ).

cnf(c183,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c184,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | q(f(X)) ) ).

cnf(c185,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | qq(f(X)) ) ).

cnf(c186,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ q(f(X)) ) ).

cnf(c187,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c188,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | q(f(X)) ) ).

cnf(c189,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c190,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ q(f(X)) ) ).

cnf(c191,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | qq(f(X)) ) ).

cnf(c192,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | q(f(X)) ) ).

cnf(c193,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c194,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ q(f(X)) ) ).

cnf(c195,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c196,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | q(f(X)) ) ).

cnf(c197,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c198,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ q(f(X)) ) ).

cnf(c199,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ qq(f(X)) ) ).

cnf(c200,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | q(f(X)) ) ).

cnf(c201,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c202,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | pr(f(X)) ) ).

cnf(c203,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | q(f(X)) ) ).

cnf(c204,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | qq(f(X)) ) ).

cnf(c205,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ pr(f(X)) ) ).

cnf(c206,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | ~ q(f(X)) ) ).

cnf(c207,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | qq(f(X)) ) ).

cnf(c208,negated_conjecture,
    ( ~ aq(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | pr(f(X)) ) ).

cnf(c209,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ q(f(X)) ) ).

cnf(c210,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | qq(f(X)) ) ).

cnf(c211,negated_conjecture,
    ( ~ aq(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ pr(f(X)) ) ).

cnf(c212,negated_conjecture,
    ( aq(X)
    | q(X)
    | ~ q(f(X)) ) ).

cnf(c213,negated_conjecture,
    ( aq(X)
    | ~ q(X)
    | q(f(X)) ) ).

cnf(c214,negated_conjecture,
    ( aq(X)
    | qq(X)
    | ~ qq(f(X)) ) ).

cnf(c215,negated_conjecture,
    ( aq(X)
    | ~ qq(X)
    | qq(f(X)) ) ).

cnf(c216,negated_conjecture,
    ( pqr1(X)
    | pqr2(X)
    | pqr3(X)
    | pqr4(X)
    | ~ pr(X)
    | pr(f(X)) ) ).

cnf(c217,negated_conjecture,
    ( pqr1(X)
    | pqr2(X)
    | pqr3(X)
    | pqr4(X)
    | pr(X)
    | ~ pr(f(X)) ) ).

cnf(c218,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | r(X)
    | s(X)
    | r(f(X)) ) ).

cnf(c219,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | r(X)
    | s(X)
    | ~ rr(f(X)) ) ).

cnf(c220,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | s(X)
    | r(f(X)) ) ).

cnf(c221,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | s(X)
    | ~ rr(f(X)) ) ).

cnf(c222,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ r(X)
    | ~ s(X)
    | ~ r(f(X)) ) ).

cnf(c223,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ r(X)
    | ~ s(X)
    | ~ rr(f(X)) ) ).

cnf(c224,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ s(X)
    | ~ r(f(X)) ) ).

cnf(c225,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ s(X)
    | ~ rr(f(X)) ) ).

cnf(c226,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ~ r(f(X)) ) ).

cnf(c227,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | rr(f(X)) ) ).

cnf(c228,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ r(f(X)) ) ).

cnf(c229,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ rr(f(X)) ) ).

cnf(c230,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | r(f(X)) ) ).

cnf(c231,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | rr(f(X)) ) ).

cnf(c232,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | r(f(X)) ) ).

cnf(c233,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | ~ rr(f(X)) ) ).

cnf(c234,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | ~ r(f(X)) ) ).

cnf(c235,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c236,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ~ ss(X)
    | ~ r(f(X)) ) ).

cnf(c237,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c238,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | r(f(X)) ) ).

cnf(c239,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c240,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ ss(X)
    | r(f(X)) ) ).

cnf(c241,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c242,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | r(f(X)) ) ).

cnf(c243,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | rr(f(X)) ) ).

cnf(c244,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ r(f(X)) ) ).

cnf(c245,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c246,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | r(f(X)) ) ).

cnf(c247,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c248,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ r(f(X)) ) ).

cnf(c249,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | rr(f(X)) ) ).

cnf(c250,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | r(f(X)) ) ).

cnf(c251,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c252,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ r(f(X)) ) ).

cnf(c253,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c254,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | r(f(X)) ) ).

cnf(c255,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c256,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ r(f(X)) ) ).

cnf(c257,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ rr(f(X)) ) ).

cnf(c258,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | r(f(X)) ) ).

cnf(c259,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c260,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | ~ qq(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | qs(f(X)) ) ).

cnf(c261,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | r(f(X)) ) ).

cnf(c262,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | rr(f(X)) ) ).

cnf(c263,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | qq(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ qs(f(X)) ) ).

cnf(c264,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | ~ r(f(X)) ) ).

cnf(c265,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | rr(f(X)) ) ).

cnf(c266,negated_conjecture,
    ( ~ ar(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | qs(f(X)) ) ).

cnf(c267,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ r(f(X)) ) ).

cnf(c268,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | rr(f(X)) ) ).

cnf(c269,negated_conjecture,
    ( ~ ar(X)
    | q(X)
    | qq(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ qs(f(X)) ) ).

cnf(c270,negated_conjecture,
    ( ar(X)
    | r(X)
    | ~ r(f(X)) ) ).

cnf(c271,negated_conjecture,
    ( ar(X)
    | ~ r(X)
    | r(f(X)) ) ).

cnf(c272,negated_conjecture,
    ( ar(X)
    | rr(X)
    | ~ rr(f(X)) ) ).

cnf(c273,negated_conjecture,
    ( ar(X)
    | ~ rr(X)
    | rr(f(X)) ) ).

cnf(c274,negated_conjecture,
    ( qrs1(X)
    | qrs2(X)
    | qrs3(X)
    | qrs4(X)
    | ~ qs(X)
    | qs(f(X)) ) ).

cnf(c275,negated_conjecture,
    ( qrs1(X)
    | qrs2(X)
    | qrs3(X)
    | qrs4(X)
    | qs(X)
    | ~ qs(f(X)) ) ).

cnf(c276,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | s(X)
    | t(X)
    | s(f(X)) ) ).

cnf(c277,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | s(X)
    | t(X)
    | ~ ss(f(X)) ) ).

cnf(c278,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | t(X)
    | s(f(X)) ) ).

cnf(c279,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | t(X)
    | ~ ss(f(X)) ) ).

cnf(c280,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ s(X)
    | ~ t(X)
    | ~ s(f(X)) ) ).

cnf(c281,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ s(X)
    | ~ t(X)
    | ~ ss(f(X)) ) ).

cnf(c282,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ t(X)
    | ~ s(f(X)) ) ).

cnf(c283,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ t(X)
    | ~ ss(f(X)) ) ).

cnf(c284,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | ~ s(f(X)) ) ).

cnf(c285,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | ss(f(X)) ) ).

cnf(c286,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ s(f(X)) ) ).

cnf(c287,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ ss(f(X)) ) ).

cnf(c288,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | s(f(X)) ) ).

cnf(c289,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | ss(f(X)) ) ).

cnf(c290,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | s(f(X)) ) ).

cnf(c291,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | ~ ss(f(X)) ) ).

cnf(c292,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ~ s(f(X)) ) ).

cnf(c293,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c294,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | ~ tt(X)
    | ~ s(f(X)) ) ).

cnf(c295,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c296,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | s(f(X)) ) ).

cnf(c297,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c298,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ tt(X)
    | s(f(X)) ) ).

cnf(c299,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c300,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | s(f(X)) ) ).

cnf(c301,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | ss(f(X)) ) ).

cnf(c302,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ s(f(X)) ) ).

cnf(c303,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c304,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | s(f(X)) ) ).

cnf(c305,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c306,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ s(f(X)) ) ).

cnf(c307,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | ss(f(X)) ) ).

cnf(c308,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | s(f(X)) ) ).

cnf(c309,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c310,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ s(f(X)) ) ).

cnf(c311,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c312,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | s(f(X)) ) ).

cnf(c313,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c314,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ s(f(X)) ) ).

cnf(c315,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ ss(f(X)) ) ).

cnf(c316,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | s(f(X)) ) ).

cnf(c317,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c318,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | ~ rr(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | rt(f(X)) ) ).

cnf(c319,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | s(f(X)) ) ).

cnf(c320,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ss(f(X)) ) ).

cnf(c321,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | rr(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ rt(f(X)) ) ).

cnf(c322,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ~ s(f(X)) ) ).

cnf(c323,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ss(f(X)) ) ).

cnf(c324,negated_conjecture,
    ( ~ as(X)
    | ~ r(X)
    | ~ rr(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | rt(f(X)) ) ).

cnf(c325,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ s(f(X)) ) ).

cnf(c326,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ss(f(X)) ) ).

cnf(c327,negated_conjecture,
    ( ~ as(X)
    | r(X)
    | rr(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ rt(f(X)) ) ).

cnf(c328,negated_conjecture,
    ( as(X)
    | s(X)
    | ~ s(f(X)) ) ).

cnf(c329,negated_conjecture,
    ( as(X)
    | ~ s(X)
    | s(f(X)) ) ).

cnf(c330,negated_conjecture,
    ( as(X)
    | ss(X)
    | ~ ss(f(X)) ) ).

cnf(c331,negated_conjecture,
    ( as(X)
    | ~ ss(X)
    | ss(f(X)) ) ).

cnf(c332,negated_conjecture,
    ( rst1(X)
    | rst2(X)
    | rst3(X)
    | rst4(X)
    | ~ rt(X)
    | rt(f(X)) ) ).

cnf(c333,negated_conjecture,
    ( rst1(X)
    | rst2(X)
    | rst3(X)
    | rst4(X)
    | rt(X)
    | ~ rt(f(X)) ) ).

cnf(c334,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | t(X)
    | p(X)
    | t(f(X)) ) ).

cnf(c335,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | t(X)
    | p(X)
    | ~ tt(f(X)) ) ).

cnf(c336,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | p(X)
    | t(f(X)) ) ).

cnf(c337,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | p(X)
    | ~ tt(f(X)) ) ).

cnf(c338,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ t(X)
    | ~ p(X)
    | ~ t(f(X)) ) ).

cnf(c339,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ t(X)
    | ~ p(X)
    | ~ tt(f(X)) ) ).

cnf(c340,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ p(X)
    | ~ t(f(X)) ) ).

cnf(c341,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ p(X)
    | ~ tt(f(X)) ) ).

cnf(c342,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | ~ t(f(X)) ) ).

cnf(c343,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | tt(f(X)) ) ).

cnf(c344,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ t(f(X)) ) ).

cnf(c345,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ tt(f(X)) ) ).

cnf(c346,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | t(f(X)) ) ).

cnf(c347,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | tt(f(X)) ) ).

cnf(c348,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | t(f(X)) ) ).

cnf(c349,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | ~ tt(f(X)) ) ).

cnf(c350,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | ~ t(f(X)) ) ).

cnf(c351,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c352,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | ~ pp(X)
    | ~ t(f(X)) ) ).

cnf(c353,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c354,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | t(f(X)) ) ).

cnf(c355,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c356,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ pp(X)
    | t(f(X)) ) ).

cnf(c357,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c358,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | t(f(X)) ) ).

cnf(c359,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | tt(f(X)) ) ).

cnf(c360,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ t(f(X)) ) ).

cnf(c361,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c362,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | t(f(X)) ) ).

cnf(c363,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c364,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ t(f(X)) ) ).

cnf(c365,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | tt(f(X)) ) ).

cnf(c366,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | t(f(X)) ) ).

cnf(c367,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c368,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ t(f(X)) ) ).

cnf(c369,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c370,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | t(f(X)) ) ).

cnf(c371,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c372,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ t(f(X)) ) ).

cnf(c373,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ tt(f(X)) ) ).

cnf(c374,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | t(f(X)) ) ).

cnf(c375,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c376,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ~ ss(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | sp(f(X)) ) ).

cnf(c377,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | t(f(X)) ) ).

cnf(c378,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | tt(f(X)) ) ).

cnf(c379,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ss(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ sp(f(X)) ) ).

cnf(c380,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | ~ t(f(X)) ) ).

cnf(c381,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | tt(f(X)) ) ).

cnf(c382,negated_conjecture,
    ( ~ at(X)
    | ~ s(X)
    | ~ ss(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | sp(f(X)) ) ).

cnf(c383,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ t(f(X)) ) ).

cnf(c384,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | tt(f(X)) ) ).

cnf(c385,negated_conjecture,
    ( ~ at(X)
    | s(X)
    | ss(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ sp(f(X)) ) ).

cnf(c386,negated_conjecture,
    ( at(X)
    | t(X)
    | ~ t(f(X)) ) ).

cnf(c387,negated_conjecture,
    ( at(X)
    | ~ t(X)
    | t(f(X)) ) ).

cnf(c388,negated_conjecture,
    ( at(X)
    | tt(X)
    | ~ tt(f(X)) ) ).

cnf(c389,negated_conjecture,
    ( at(X)
    | ~ tt(X)
    | tt(f(X)) ) ).

cnf(c390,negated_conjecture,
    ( stp1(X)
    | stp2(X)
    | stp3(X)
    | stp4(X)
    | ~ sp(X)
    | sp(f(X)) ) ).

cnf(c391,negated_conjecture,
    ( stp1(X)
    | stp2(X)
    | stp3(X)
    | stp4(X)
    | sp(X)
    | ~ sp(f(X)) ) ).

cnf(c392,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | p(X)
    | q(X)
    | p(f(X)) ) ).

cnf(c393,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | p(X)
    | q(X)
    | ~ pp(f(X)) ) ).

cnf(c394,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | q(X)
    | p(f(X)) ) ).

cnf(c395,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | q(X)
    | ~ pp(f(X)) ) ).

cnf(c396,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ p(X)
    | ~ q(X)
    | ~ p(f(X)) ) ).

cnf(c397,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ p(X)
    | ~ q(X)
    | ~ pp(f(X)) ) ).

cnf(c398,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ q(X)
    | ~ p(f(X)) ) ).

cnf(c399,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ q(X)
    | ~ pp(f(X)) ) ).

cnf(c400,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | ~ p(f(X)) ) ).

cnf(c401,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | pp(f(X)) ) ).

cnf(c402,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ p(f(X)) ) ).

cnf(c403,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ pp(f(X)) ) ).

cnf(c404,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | p(f(X)) ) ).

cnf(c405,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | pp(f(X)) ) ).

cnf(c406,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | p(f(X)) ) ).

cnf(c407,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | ~ pp(f(X)) ) ).

cnf(c408,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | ~ p(f(X)) ) ).

cnf(c409,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c410,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | ~ qq(X)
    | ~ p(f(X)) ) ).

cnf(c411,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c412,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | p(f(X)) ) ).

cnf(c413,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c414,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ qq(X)
    | p(f(X)) ) ).

cnf(c415,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c416,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | p(f(X)) ) ).

cnf(c417,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | ~ p(X)
    | ~ pp(X)
    | q(X)
    | pp(f(X)) ) ).

cnf(c418,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | ~ p(f(X)) ) ).

cnf(c419,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | p(X)
    | ~ pp(X)
    | q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c420,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | p(f(X)) ) ).

cnf(c421,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ p(X)
    | ~ pp(X)
    | ~ q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c422,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | ~ p(f(X)) ) ).

cnf(c423,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | p(X)
    | ~ pp(X)
    | ~ q(X)
    | pp(f(X)) ) ).

cnf(c424,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | p(f(X)) ) ).

cnf(c425,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c426,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ p(f(X)) ) ).

cnf(c427,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c428,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | p(f(X)) ) ).

cnf(c429,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c430,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ p(f(X)) ) ).

cnf(c431,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ pp(f(X)) ) ).

cnf(c432,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | p(f(X)) ) ).

cnf(c433,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c434,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | ~ tt(X)
    | p(X)
    | pp(X)
    | ~ q(X)
    | qq(X)
    | tq(f(X)) ) ).

cnf(c435,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | p(f(X)) ) ).

cnf(c436,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | pp(f(X)) ) ).

cnf(c437,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | tt(X)
    | p(X)
    | pp(X)
    | q(X)
    | ~ qq(X)
    | ~ tq(f(X)) ) ).

cnf(c438,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | ~ p(f(X)) ) ).

cnf(c439,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | pp(f(X)) ) ).

cnf(c440,negated_conjecture,
    ( ~ ap(X)
    | ~ t(X)
    | ~ tt(X)
    | ~ p(X)
    | pp(X)
    | q(X)
    | qq(X)
    | tq(f(X)) ) ).

cnf(c441,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ p(f(X)) ) ).

cnf(c442,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | pp(f(X)) ) ).

cnf(c443,negated_conjecture,
    ( ~ ap(X)
    | t(X)
    | tt(X)
    | ~ p(X)
    | pp(X)
    | ~ q(X)
    | ~ qq(X)
    | ~ tq(f(X)) ) ).

cnf(c444,negated_conjecture,
    ( ap(X)
    | p(X)
    | ~ p(f(X)) ) ).

cnf(c445,negated_conjecture,
    ( ap(X)
    | ~ p(X)
    | p(f(X)) ) ).

cnf(c446,negated_conjecture,
    ( ap(X)
    | pp(X)
    | ~ pp(f(X)) ) ).

cnf(c447,negated_conjecture,
    ( ap(X)
    | ~ pp(X)
    | pp(f(X)) ) ).

cnf(c448,negated_conjecture,
    ( tpq1(X)
    | tpq2(X)
    | tpq3(X)
    | tpq4(X)
    | ~ tq(X)
    | tq(f(X)) ) ).

cnf(c449,negated_conjecture,
    ( tpq1(X)
    | tpq2(X)
    | tpq3(X)
    | tpq4(X)
    | tq(X)
    | ~ tq(f(X)) ) ).

%--------------------------------------------------------------------------
