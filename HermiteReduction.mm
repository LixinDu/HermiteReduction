#################################################################################################
## Copyright (c) December 2022, JKU. All rights reserved.
## Author: Lixin Du <lixin.du@jku.at>
## Load the file: integral_bases.txt (by Shayea Aldossari) ## [Dx, x]
## Load the modules:
##          LinearRelation (in HermiteCT.mm, by Shaoshi Chen <schen@amss.ac.cn>)
## Modified on February 3, 2023
#################################################################################################


HermiteReduction := module()
      description "Hermite reduction and creative telescoping for D-finite functions via integral bases";
      export
                DiffOperator,
                StandardForm,
                DiffOperator2,
                BasisMatrix,
                CoeffOperator,
                FromCoeffToOperator,
                HR,
                AdditiveDecomposition,
                CreativeTelescoping,
                VerifyTelescoper,
                Verify_HR;

      local
                mydenom,
                ModPoly, ## local
                ModPoly_infty, ## local
                ModLinearSolve, ## local
                ModLinearSolve_infty, ## local
                HR_one_place, ## algebraic and dfinite
                HR_at_infinity, ## algebraic and dfinite
                HR_step, ## algebraic and dfinite
                HR_step_dfinite,
                CoeffOfPolyMatrices, ## algebraic and dfinite
                FromCoeffToPolyVector, ## algebraic and dfinite
                Representation_coeff, ## local
                IntegrableReminder, ## algebraic and dfinite
                GenerateBasis, ## algebraic and dfinite
                ProjectiveComponent, ## algebraic and dfinite
                myReverseVector, ## algebraic and dfinite
                myReverseMatrix, ## algebraic and dfinite
                Verify_HR_step, ## local
                Verify_HR_step_dfinite; ## local
      option
                package;


##############################################################################################################
# Export
# Name: Mydenom
# Calling sequence:
#                    Mydenom(M, x)
# Input:  M,  a matrix over C(x),
#         x,  a variable name;
# Output: e,  the lcm of the denominator of all entries of M w.r.t. x
# Example: M := Matrix(2, 2, [[1/(x+2), 1/x^3], [0, -2/x^3]]);
#          mydenom(M, x);
####################################I###########################################################################

mydenom := proc(M, x)
    local M_, M_denom;
    M_ := map(normal, M);
    M_denom := primpart(lcm(op(map(denom,convert(M,list)))), x);
end proc:


##############################################################################################################
# Export
# Name: DiffOperator
# Calling sequence:
#                    DiffOperator(f, Dx, x, L)
# Input:  f,  an operator in C(x)[Dx];
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: g, where g + <L> in is the derivation of f + <L> with respect to x.
# Example: L :=x^3*Dx^2+(2+3*x^2)*Dx;
#          f := x^3*Dx;
#          DiffOperator(f,Dx,x,L);
####################################I###########################################################################

DiffOperator := proc(f, Dx, x, L)
    local A, L_ore, f_ore, df_ore, df_rem, df;
    A := OreTools:-SetOreRing(x, 'differential');
    L_ore := (OreTools[Converters]):-FromPolyToOrePoly(L, Dx);
    f_ore := (OreTools[Converters]):-FromPolyToOrePoly(f, Dx);
    df_ore := OreTools:-Multiply(OrePoly(0,1), f_ore, A);
    df_rem := OreTools:-Remainder['right'](df_ore, L_ore, A); ## f=QL+R
    df := (OreTools[Converters]):-FromOrePolyToPoly(df_rem, Dx);
end proc:


##############################################################################################################
# Export
# Name: StandardForm
# Calling sequence:
#                    Standard(f, ann, Der_x, Der_t)
# Input:  f,  an operator in C(x, t)[Dx, Dt];
#         ann,  ann = [L, P] where L in C(x,t)[Dx] and P = c*Dt - U_t with c in C(x,t) and U_t in C(x, t)[Dx];
#         Der_x, Der_x = [Dx, x], where Dx is a differential operator with repect to x and x is a variable name;
#         Der_t, Der_t = [Dt, t], where Dt is a differential operator with repect to t and t is a variable name.
# Output: g, where g in C(x, t)[Dx] with ord(g, Dx) < ord(L, Dx) such that
# Output: g, where g in C(x, t)[Dx] with ord(g, Dx) < ord(L, Dx) such that
#                            g + ann = f + ann
#            in C(x, t)[Dx, Dt]/ann.
# Remark: In this setting, {1, Dx, ..., Dx^{n-1}} is a basis of C(x, t)[Dx, Dt]/ann, where n = ord(L);
# Example: ann := [Dx - (t^3 + (-2*x + 1)*t^2 + 1)/(t - 2*x + 1), Dt - (4*t^2*x + (-8*x^2 + 4*x)*t - 1)/(2*t - 4*x + 2)]
#          f := Dt^2 + Dx;
#          StandardForm(f, ann, [Dx, x], [Dt, t])
####################################I###########################################################################

StandardForm := proc(f, ann, Der_x, Der_t);
    local L, P, Dx, x, Dt, t, OreRing_x, OreRing_t, f_ore, P_ore, f_rem, g, g_ore, g_rem, r, L_ore;
    L := ann[1];
    P := ann[2];
    Dx, x := op(Der_x);
    Dt, t := op(Der_t);

    #### compute g (free of Dt) such that g = f mod P ####
    OreRing_t := OreTools:-SetOreRing(t, 'differential');
    f_ore := (OreTools[Converters]):-FromPolyToOrePoly(f, Dt);
    P_ore := (OreTools[Converters]):-FromPolyToOrePoly(P, Dt);
    f_rem := OreTools:-Remainder['right'](f_ore, P_ore, OreRing_t); ## f=QP+g
    g := (OreTools[Converters]):-FromOrePolyToPoly(f_rem, Dt);


    #### compute r (ord(r, Dx) < ord(L, Dx)) such that r = g mod L, then r = f mod ann ####
    OreRing_x := OreTools:-SetOreRing(x, 'differential');
    g_ore := (OreTools[Converters]):-FromPolyToOrePoly(g, Dx);
    L_ore := (OreTools[Converters]):-FromPolyToOrePoly(L, Dx);
    g_rem := OreTools:-Remainder['right'](g_ore, L_ore, OreRing_x); ## g=QL+r
    r := (OreTools[Converters]):-FromOrePolyToPoly(g_rem, Dx);

end proc:



##############################################################################################################
# Export
# Name: DiffOperator2
# Calling sequence:
#                    DiffOperator2(f, ann, t, Der_x, Der_t)
#                    DiffOperator2(f, ann, t, Der_x, Der_t, i)
# Input:  f,  an operator in C(x, t)[Dx, Dt];
#         ann,  ann = [L, P] where L in C(x,t)[Dx] and P = c*Dt - U_t with c in C(x, t) and U_t in C(x, t)[Dx];
#         t, a variable name;
#         Der_x, Der_x = [Dx, x], where Dx is a differential operator with repect to x and x is a variable name;
#         Der_t, Der_t = [Dt, t], where Dt is a differential operator with repect to t and t is a variable name.
# Output: g, where g in C(x, t)[Dx] such that g + ann = Dt^i*f + ann with respect to t in C(x, t)[Dx, Dt]/ann.
#            The default value for i is 1.
# Remark: In this setting, {1, Dx, ..., Dx^{n-1}} is a basis of C(x, t)[Dx, Dt]/ann, where n = ord(L);
# Example: f := 1;
#          ann := [Dx^2 + 4*x*Dx +(2+t^2+4*x^2), Dt - x/t*Dx - 2*x^2/t];
#          DiffOperator2(f, ann, t, [Dx, x], [Dt, t]);
#          DiffOperator2(f, ann, t, [Dx, x], [Dt, t], 2);
####################################I###########################################################################

DiffOperator2 := proc(f, ann, t, Der_x, Der_t, i);
    local L, P, Dx, x, Dt, A, f_ore, Dt_ore, df_ore, df;
    L := ann[1];
    P := ann[2];
    Dx, x := op(Der_x);
    Dt := Der_t[1];

    A := OreTools:-SetOreRing(Der_t[2], 'differential');

    f_ore := (OreTools[Converters]):-FromPolyToOrePoly(f, Dt);
    Dt_ore :=  (OreTools[Converters]):-FromPolyToOrePoly(Dt, Dt);

    #### differentiate f with respect to t #####
    df_ore := OreTools:-Multiply(Dt_ore, f_ore, A);
    df := (OreTools[Converters]):-FromOrePolyToPoly(df_ore, Dt);
    df := StandardForm(df, ann, Der_x, Der_t);

    if nargs = 5 then
        return df;
    elif i = 1 then
        return df;
    else
        DiffOperator2(df, ann, t, Der_x, Der_t, i-1);
    fi;
end proc:


##############################################################################################################
# Export
# Name: BasisMatrix
# Calling sequence:
#                    BasisMatrix(W, Dx, x, L)
# Input:  W,  a basis of C(x)[Dx]/<L> represented by a list;
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: M, where M is a matrix over C(x) such that W'=MW.
# Example: L :=(x^3 - x^2)*Dx^2 + (-x^2 + x - 1)*Dx + 1;
#          W := [1, Dx];
#          BasisMatrix(W, Dx, x, L);
####################################I###########################################################################

BasisMatrix := proc(W, Dx, x, L)
    local diff_W, n, coeff_dw, coeff_w, M;
    diff_W := map(f->DiffOperator(f, Dx, x, L), W);
    n := degree(L, Dx);
    coeff_dw := Matrix(n, (i,j)-> coeff(diff_W[i], Dx, j-1));
    coeff_w := Matrix(n, (i,j)-> coeff(W[i], Dx, j-1));
    M := LinearAlgebra:-MatrixMatrixMultiply(coeff_dw,LinearAlgebra:-MatrixInverse(coeff_w));
    M := map(normal, M);
end proc:


##############################################################################################################
# Export
# Name: CoeffOperator
# Calling sequence:
#                    CoeffOperator(f, W, Dx, x, L)
# Input:  f,  an operator in C(x)[Dx]/<L>
#         W,  a basis of C(x)[Dx]/<L> represented by a list;
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: a, where a is the coefficient vector of f such that f = aW.
# Example: f := -1-2/ x^2 + (-2+3*x^2 -3*x^4)*Dx/x;
#          W := [1,x*Dx];
#          L := x^3*Dx^2+(2+3*x^2)*Dx;
#          Coeff_operator(f, W, Dx, x, L);
####################################I###########################################################################

CoeffOperator := proc(f, W, Dx, x, L)
    local coeff_f, coeff_w, n;
    n := degree(L,Dx);

    ## coefficient w.r.t. the standard basis [1, Dx, ..., Dx^{n-1}]
    coeff_f := LinearAlgebra:-Transpose(Vector(n, i->coeff(f,Dx,i-1)));
    coeff_w := Matrix(n, (i,j)-> coeff(W[i], Dx, j-1));

    ## coefficient w.r.t. a basis W
    coeff_f := LinearAlgebra:-MatrixMatrixMultiply(coeff_f, LinearAlgebra:-MatrixInverse(coeff_w));
end proc:


##############################################################################################################
# Export
# Name: FromCoeffToOperator
# Calling sequence:
#                    FromCoeffToOperator(f_coeff, W)
# Input:  f_coeff,  a vector in C(x)^n
#         W,  a basis of C(x)[Dx]/<L> represented by a list;
# Output: f, where f = f_coeff.W.
# Example: f_coeff := Vector[row](2, [-1 - 2/x^2, (-3*x^4 + 3*x^2 - 2)/(x^4*(x + 2)^2)]);
#          W := [1,x^3*Dx];
#          FromCoeffToOperator(f_coeff, W);
####################################I###########################################################################

FromCoeffToOperator := proc(f_coeff, W)
    local basis, f;
    basis := Vector[column](nops(W),i->W[i]);
    f := f_coeff.basis;
end proc:



##############################################################################################################
# Export
# Name: ModPoly
# Calling sequence:
#                    ModPoly(a, b, x)
# Input:  a,  a rational function in x whose denominator is coprime to b;
#         b,  a polynoimal in x;
#         x,  a variable name.
# Output: c,  where c is polynomial in x such that c = a mod b
# Example: a := 1/3*x^4 + 2/3*x^2;
#          b := x^3;
#          ModPoly(a, b, x);
####################################I###########################################################################

ModPoly := proc(a, b, x)
    local gcd_db, a_mod, d, s, t;
    d := denom(normal(a));
    gcd_db := gcdex(d, b, x, 's','t'); ## s d + t b = 1
    if gcd_db = 1 then
        a_mod := rem(normal(a*d*s), b, x);
    else
        ## printf("%d and %d are not coprime", d, b);
        error "invalid to modulo by a polynomial"
    fi;
    a_mod;
end proc:


##############################################################################################################
# Export
# Name: ModPoly_infty
# Calling sequence:
#                    ModPoly_infty(a, b, x)
# Input:  a,  a rational function in x whose denominator is coprime to b;
#         b,  a power of 1/x;
#         x,  a variable name.
# Output: c,  where c is polynomial in 1/x such that c = a mod b
# Example: a := -(4*x^5 - 3)/(9*x^2*(x^3 + 1)); # a := 4/9;
#          b := 1/x^4;
#          ModPoly_infty(a, b, x);
####################################I###########################################################################

ModPoly_infty := proc(a, b, x)
    local a1, b1, a1_mod, a_mod;
    a1 := subs(x=1/z, a);
    b1 := subs(x=1/z, b);
    a1_mod := ModPoly(a1, b1, z);
    a_mod := subs(z=1/x, a1_mod);
end proc:



##############################################################################################################
# Export
# Name: ModLinearSolve
# Calling sequence:
#                    ModLinearSolve(a, B, v, x)
# Input:  a,  a column vector in C(x)^n;
#         B,  a matrix over C(x) of dimension n;
#         v,  a polynomial in x;
#         x,  a variable name.
# Output: b,  where b is a vector in C[x]^n such that b is a (unique) solution of the linear congruence system
#                         Bb = a mod v
# Remark: We require the linear systme Bb = a has a unique solution in C(x) and the denominator of such a solution is
#         coprime to v. So it is valid to modulo b by v.
# Example: a := Vector[column](2, [-x^2*(x^2 + 2)*x^2, (-3*x^4 + 3*x^2 - 2)*x^2]);
#          B := Matrix(2, 2, [[-3*x^2, 0], [1, -3*x^2 - 2]]);
#          v := x^3;
#          ModLinearSolve(a, B, v, x).
####################################I###########################################################################

ModLinearSolve := proc (a, B, v, x)
    local sol, sol_mod, n;
    n := LinearAlgebra:-Dimension(a);
    sol := LinearAlgebra:-LinearSolve(B, a);
    sol_mod := Vector(n, i -> ModPoly(sol[i], v, x));
end proc:


##############################################################################################################
# Export
# Name: ModLinearSolve_infty
# Calling sequence:
#                    ModLinearSolve_infty(a, B, v, x)
# Input:  a,  a column vector in C(x)^n;
#         B,  a matrix over C(x) of dimension n;
#         v,  a power of 1/x;
#         x,  a variable name.
# Output: b,  where b is a vector in C(x)_infty^n/<v> (a subring of C[[1/x]]^n/<v>) such that b is a (unique) solution
#             of the linear congruence system
#                         Bb = a mod v
# Remark: We require the linear systme Bb = a has a unique solution in C(x) and the denominator of such a solution is
#         invertible in C[[1/x]]. So it is valid to modulo b by v.
# Example: a:=Vector[column](2, [4/x^3, 1/x^5]);
#          B:=Matrix([[3/(x^3),0],[1,3+3/(x^3)]]);
#          v :=1/x^4;
#          ModLinearSolve_infty(a, B, v, x);
####################################I###########################################################################

ModLinearSolve_infty := proc (a, B, v, x)
    local sol, sol_mod, n;
    n := LinearAlgebra:-Dimension(a);
    sol := LinearAlgebra:-LinearSolve(B, a);
    sol_mod := Vector(n, i -> ModPoly_infty(sol[i], v, x));
end proc:


########################################################################################################################
# Export
# Name: HR_one_place
# Calling sequence:
#                    HR_one_place(f_coeff, M, v, x)
# Input:  f_coeff,  a vector in C(x)^n, representing the coefficients of f with respect to an integral basis W;
#         M,  a matrix over C(x) such that W' = M W;
#         v,  an irreducible polynomial in x;
#         x,  a variable name.
# Output: g_coeff, h_coeff, which are coefficents of g, h with respect to W such that
#                          f = g' + h
#         and h is an Hermite remainder at v.
# Example: f_coeff := Vector[row](2, [-1 - 2/x^2, (-3*x^4 + 3*x^2 - 2)/x^4/(x+2)^2]);
#          M := Matrix(2, 2, [[0, 1/x^3], [0, -2/x^3]]);
#          v := x;
#          HR_one_place(f_coeff, M, v, x);
# Remark: this procedure will be used in both the algebraic ann the D-finite cases.
####################################I###################################################################################

HR_one_place := proc(f_coeff, M, v, x)
    local e, f_denom, d, n, sol, lambda, g, h, u, a, In, B, b, g_coeff, h_coeff, h_cert, h_rem;
    e := lcm(op(map(denom,convert(M,list))));
    f_denom := lcm(op(map(denom,convert(f_coeff,list))));
    d := padic:-orderp(f_denom, v, x);
    lambda := padic:-orderp(e, v, x);  ## lambda >= 0, since e is a polynomial
    n := LinearAlgebra:-Dimension(f_coeff);

    #### f_coeff is an Hermite reminder at v
    if d <= max(1,lambda) then
        g := LinearAlgebra:-ZeroVector[row](n);
        h := f_coeff;
        return g,h;
    fi;

    #### reduce the multiplicity d of an irreducible factor v
    if lambda = 0 then
        a := simplify(u*v^d*f_coeff);
        sol := -((d-1)*u*diff(v,x))^(-1)*a;
        b := Vector[row](n, i -> ModPoly(sol[i], v, x));
    elif lambda >=1 then
        u := f_denom/v^d;
        a := simplify(u*v^(d+lambda-1)*f_coeff);
        In := LinearAlgebra:-IdentityMatrix(n);
        B := u*v^lambda*M-(d-1)*u*v^(lambda-1)*diff(v,x)*In;
        a := LinearAlgebra:-Transpose(a);
        B := LinearAlgebra:-Transpose(B);
        b := LinearAlgebra:-Transpose(ModLinearSolve(a, B, v^lambda, x));
    fi;

    g_coeff := b/v^(d-1);
    h_coeff := simplify(f_coeff - diff(g_coeff,x)- g_coeff.M);
    h_cert, h_rem := HR_one_place(h_coeff, M, v, x);
    g := g_coeff + h_cert;
    h := h_rem;

    return g, h;
end proc:



########################################################################################################################
# Export
# Name: HR_at_infinity
# Calling sequence:
#                    HR_at_infinity(f_coeff, M, x)
# Input:  f_coeff,  a vector in C(x)^n, representing the coefficients of f with respect to an integral basis W;
#         M,  a matrix over C(x) such that W' = M W;
#         v,  an irreducible polynomial in x;
#         x,  a variable name.
# Output: g_coeff, h_coeff, which are coefficents of g, h with respect to W such that
#                          f = g' + h
#         and h is an Hermite remainder at v.
# Example1: f_coeff := Vector[row](2, [1/3*(-3*x^2 - 4)/x^2, 1/3*(-9*x^2 + 13)/x^2]);
#           M := Matrix(2, 2, [[0, 1/x^3], [0, -2/x^3]]);
#           HR_at_infinity(f_coeff, M, x);
# Example2: nonfuchsian at infinity
#           f_coeff := Vector[row](2, [4*x^3, x])
#           M := Matrix(2, 2, [[0, x^2], [0, 3*x^2]])
#           HR_at_infinity(f_coeff, M, x);
# Remark: this procedure will be used in both the algebraic and the D-finite cases.
####################################I###################################################################################

HR_at_infinity := proc(f_coeff, M, x)
    local deg, d, lambda, n, g, h, a, sol, b, In, B, g_coeff, h_coeff, h_cert, h_rem;
    deg := f -> - padic:-orderp(f, 1/x, x);
    d := max(map(deg, f_coeff));
    lambda := max(map(deg, M));
    n := LinearAlgebra:-Dimension(f_coeff);

    #### f_coeff is an Hermite reminder at infinity
    if d < max(0,lambda) then
        g := LinearAlgebra:-ZeroVector[row](n);
        h := f_coeff;
        return g,h;
    fi;

    #### reduce the degree in x
    if lambda < -1 then
        a := simplify(x^(-d)*f_coeff); ## f_coeff = x^d*a
        sol := (d + 1)^(-1)*a;
        b := Vector[row](n, i -> ModPoly_infty(sol[i], 1/x, x)); ## b = sol mod 1/x
    else ## lambda >= -1
        a := simplify(x^(-d-lambda-1)*f_coeff);
        In := LinearAlgebra:-IdentityMatrix(n);
        B := x^(-lambda)*M + (d+1)*x^(-lambda-1)*In;
        a := LinearAlgebra:-Transpose(a);
        B := LinearAlgebra:-Transpose(B);
        b := LinearAlgebra:-Transpose(ModLinearSolve_infty(a, B,x^(-lambda-2), x));
    fi;

    g_coeff := simplify(x^(d+1)*b);
    M;
    h_coeff := simplify(f_coeff - diff(g_coeff,x)- g_coeff.M);
    h_cert, h_rem := HR_at_infinity(h_coeff, M, x);
    g := g_coeff + h_cert;
    h := h_rem;

    return g, h;
end proc:



########################################################################################################################
# Export
# Name: HR_step
# Calling sequence:
#                    HR_step(f_coeff, M, x)
# Input:  f_coeff,  a vector in C(x)^n, representing the coefficients of f with respect to an integral basis W
#         M,  a matrix over C(x) such that W' = M W;
#         x,  a variable name.
# Output: g_coeff, h_coeff, which are coefficents of g, h with respect to W such that
#                    f = g' + h
#         and h is an Hermite remainder at all finite places.
# Example: f_coeff := Vector[row](2, [-1 - 2/x^2, (-3*x^4 + 3*x^2 - 2)/x^4/(x+2)^2]);
#          M := Matrix(2, 2, [[0, 1/x^3], [0, -2/x^3]]);
#          HR_one_place(f_coeff, M, v, x);
# Remark: this procedure will be used in both the algebraic ann the D-finite cases.
####################################I###################################################################################

HR_step := proc(f_coeff, M, x)
    local e, f_denom, lc, factorlist, n, f, g, h, pair, v, g_coeff, h_coeff;
    e := primpart(lcm(op(map(denom,convert(normal(M),list)))),x);
    f_denom := primpart(lcm(op(map(denom,convert(normal(f_coeff),list)))),x);
    lc, factorlist := op(factors(f_denom));
    n := LinearAlgebra:-Dimension(f_coeff);

    f := f_coeff;
    g := LinearAlgebra:-ZeroVector[row](n);
    h := f_coeff;

    for pair in factorlist do
        v := pair[1];
        g_coeff, h_coeff := HR_one_place(h, M, v, x);
        g := g + g_coeff;
        h := h_coeff;
    od;
    g, h;
end proc:


########################################################################################################################
# Export
# Name: Verify_HR_step
# Calling sequence:
#                    Verify_HR_step(f_coeff, g_coeff, h_coeff, M, x)
# Input:  f_coeff,  a vector in C(x)^n, representing the coefficients of f with respect to an integral basis W;
#         g_coeff,  a vector in C(x)^n, representing the coefficients of g with respect to an integral basis W;
#         h_coeff,  a vector in C(x)^n, representing the coefficients of h with respect to an integral basis W;
#         M,  a matrix over C(x) such that W' = M W;
#         x,  a variable name.
# Output: true, if  f = g' + h, i.e., f_coeff.W = (g_coeff.W)' + (h_coeff.W);
#         false, otherwise.
# Remark: this procedure will be used in both the algebraic ann the D-finite cases.
####################################I###################################################################################

Verify_HR_step := proc(f_coeff, g_coeff, h_coeff, M, x)
    local r;
    r := simplify(f_coeff - diff(g_coeff,x) - g_coeff.M - h_coeff);
    Testzero(r);
end proc:


########################################################################################################################
# Export
# Name: HR_step_dfinite
# Calling sequence:
#                    HR_step_dfinite(f, W, Dx, x, L)
# Input:  f,  a vector in C(x)^n, representing the coefficients of f with respect to an integral basis W;
#         W,  an integral basis of C(x)[Dx]/<L>;
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: g_coeff, h_coeff, M, where M is a matrix over C(x) such that W' = MW,
#         g_coeff, h_coeff are coefficents of g, h with respect to W such that
#                    f = g' + h
#         and h is an Hermite remainder at all finite places.
# Example: f := -1-2/ x^2 + (-2+3*x^2 -3*x^4)*Dx/x/(x+2)^2;
#          L := x^3*Dx^2+(2+3*x^2)*Dx;
#          W := [1, x^3*Dx];
#          HR_step_dfinite(f, W, Dx, x, L);
####################################I###################################################################################

HR_step_dfinite := proc(f, W, Dx, x, L)
    local f_coeff, M, e, f_denom, g_coeff, h_coeff;
    f_coeff := CoeffOperator(f, W, Dx, x, L);;
    M := BasisMatrix(W, Dx, x, L);
    f_coeff := CoeffOperator(f, W, Dx, x, L);
    f_denom := lcm(op(map(denom,convert(f_coeff, list))));
    g_coeff, h_coeff := HR_step(f_coeff, M, x);
    g_coeff, h_coeff, M;
end proc:


########################################################################################################################
# Export
# Name: HR
# Calling sequence:
#                    HR(f, basis, Dx, x, L)
# Input:  f,  an element in C(x)[Dx]/<L>;
#         basis,  [W, degree], where W is a normalized integral basis of C(x)[Dx]/<L> and degree= [-val_infty(W[i])];
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: [g, [P1, W], [Q1, V], h],
#         where g, h in C(x)[Dx]/<L>, P1, Q1 are list of coefficients in C(x)^n, W is a normalized integral basis and
#         V is a local integral basis such that
#                    f = g' + h    with    h = P1 * W + Q1 * V
#         and h is an Hermite remainder at all finite places and at infinity.
# Example: f := -1-2/ x^2 + (-2+3*x^2 -3*x^4)*Dx/x;
#          L := x^3*Dx^2+(2+3*x^2)*Dx;
#          basis := [[x^3*Dx, 1], [0, 0]];
#          HR(f, basis, Dx, x, L);
####################################I###################################################################################


HR := proc(f, basis, Dx, x, L)
    local n, W, val_infty, T, V, g_coeff, h_coeff, M_w, e_w, h_denom, d, h_numer, P, s, t, Q, M_v, gg_coeff, hh_coeff, W_vector, V_vector, g, h, P1, Q1;
    n := degree(L, Dx);

    #### W is a normailzed integral basis and V is a local integral basis at infinity
    W := basis[1];
    val_infty := - basis[2];
    T := LinearAlgebra:-DiagonalMatrix([seq(x^val_infty[i], i = 1..n)]); ## V = TW
    V := [seq(W[i]*x^val_infty[i], i=  1..n)];

    #### Hermite reduction at all finite places
    g_coeff, h_coeff, M_w := HR_step_dfinite(f, W, Dx, x, L);

    #### split h = (P/d)*W + (Q/e)*W
    e_w := primpart(lcm(op(map(denom,convert(M_w,list)))), x);
    h_denom := primpart(lcm(op(map(denom,convert(normal(h_coeff), list)))), x);
    d := simplify(h_denom/gcd(h_denom,e_w));
    #if x in indets(d) then
        gcdex(d, e_w, x, 's', 't'); ## s*d + t*e_w = d
        h_numer := simplify(d*e_w*h_coeff);
        P := Vector[row](n, i -> rem(t*h_numer[i], d, x));
        Q := simplify((h_numer - P*e_w)/d);  ## h_coeff := simplify(h_coeff - P/d); ## or
    #else
    #    P := Vector[row](n, i -> 0);
    #    Q := h_coeff;
    #fi;


    #### Hermite reduction at infinity
    h_coeff := simplify((1/e_w)*Q.T^(-1));   ## coeff with respect to a basis V
    M_v := BasisMatrix(V, Dx, x, L);
    gg_coeff, hh_coeff := HR_at_infinity(h_coeff, M_v, x);

    #### compute a certificate g and an Hermite reminder h
    W_vector := convert(W, Vector);
    V_vector := convert(V, Vector);
    g := g_coeff.W_vector + gg_coeff.V_vector;
    h := (1/d)*P.W_vector + hh_coeff.V_vector;

    P1 := convert(P/d, list);
    Q1 := convert(hh_coeff, list);
    [g, [P1, W], [Q1, V], h];
end proc:


########################################################################################################################
# Export
# Name: CoeffOfPolyMatrices
# Calling sequence:
#                    CoeffOfPolyMatrices(matrixlist, x, ldeg, deg)
# Input:  matrixlist,  a list of matrices of dimension n over C[x, 1/x];
#         x,  a variable name;
#         ldeg, deg,  two integers such that ldeg <= deg.
# Output: coefflist,  a list of vectors over C, which represents the list of the coefficients of eahc row of all matrices
#         in the matrixlist. The coefficient of a vector in C[x]^n is the coefficient with respect to the following basis
#                            x^i * E,  i = ldeg, ..., deg,
#         where E = {e1, ..., en} is the standard basis of C^n.
# Example:  matrixlist := [Matrix(2, 2, [[-2*x^2, 1], [0, -3*x^2 - 4]])];
#           CoeffOfPolyMatrices(matrixlist, x, 0, 3);
#           # The result is [Vector[row](8, [0, 1, 0, 0, -2, 0, 0, 0]), Vector[row](8, [0, -4, 0, 0, 0, -3, 0, 0])]
# Remark: if matrixlist is a list matrices of dimension (m, n), this procedure also outputs the coefficients of each row
#         of all matrices in the matrixlist.
####################################I#####################################################################################

CoeffOfPolyMatrices := proc(matrixlist, x, ldeg, deg)
    local n, coefflist, M, i, elem, coeff_elem;
    n := LinearAlgebra:-Dimension(matrixlist[1])[1];
    coefflist := [];
    for M in matrixlist do
        for i from 1 to n do
            elem := map(normal, convert(LinearAlgebra:-Row(M, i), Matrix));
            coeff_elem := seq(MatrixPolynomialAlgebra:-Coeff(elem, x, i), i = ldeg..deg);
            coeff_elem := LinearAlgebra:-Transpose(convert([coeff_elem], Vector));
            coefflist := [op(coefflist), coeff_elem];
        od;
    od;
    coefflist;
end proc:


##############################################################################################################
# Export
# Name: FromCoeffToPolyVector
# Calling sequence:
#                    FromCoeffToPolyVector(coeffvector, mu, 'x', n)
# Input:  coeffvector,  a vector over C;
#         mu,  an integer;
#         x,  a variable name;
#         n,  a nonzero natural number.
# Output: polyvec,  a vector in C[x, 1/x] of dimension n such that coeffvector is the coefficient of polyvec
#         with respect to the following basis
#                            x^i * E,  i = mu, ..., delta,
#         where E = {e1, ..., en} is the standard basis of C^n and delta - mu + 1 = dim(coeffvector)/n.
# Example:  x := 'x';
#          coeffvector := Vector[row](6, [0, 0, 2, 1, 0, 0]);
#          mu, n := 0, 2;
#          FromCoeffToPolyVector(coeffvector, mu, 'x', n);
#          # The result is Vector[row](2, [2*x, x]).
####################################I##################################################################################

FromCoeffToPolyVector := proc(coeffvector, mu, x, n)
    local m, polyvec;
    m := LinearAlgebra:-Dimension(coeffvector)/n;
    polyvec := Vector[row](n, j -> add(coeffvector[(i-1)*n+j]*x^(mu + i - 1), i = 1..m));
end proc:


################################################################################################
# Export
# Name: Representation_coeff
# Calling sequence:
#                    Representation_coeff(V, U)
# Input:  V,  a list of vectors;
#         U,  a list of vectors, Span_C(U) is a C-subvector space of Span_C(V).
# Output: S,  a matrix in C^{m*n}, where m = nops(V), n = nops(U) such that
#                   V. Column(S, i) = U[i]
#             for all i = 1...nops(U).
###############################################################################################

Representation_coeff := proc(V, U)
    local m_v, n_v, m_u, n_u, vars, A, B, sol, free_vars, zero, y;
    m_v:= LinearAlgebra:-Dimension(V[1]);
    m_u:= LinearAlgebra:-Dimension(U[1]);
    n_v := nops(V);
    n_u := nops(U);
    vars := indets([op(U),op(V)]);
    A := Matrix(m_v,n_v, (i,j) -> V[j][i]);
    B := Matrix(m_u,n_u, (i,j) -> U[j][i]);
    sol := LinearAlgebra:-LinearSolve(A, B);
    free_vars := convert(indets(sol) minus vars, list);
    zero := convert(LinearAlgebra:-ZeroVector(nops(free_vars)), list);
    y := zip((x, y) -> x = y, free_vars, zero);
    sol := subs(y, sol);
end proc:


########################################################################################################################################
# Export
# Name: IntegrableReminder
# Calling sequence:
#                    IntegrableReminder(M_v, u, tau, x)
#                    IntegrableReminder(M_v, u, tau, x, 'integrand', 'rep_coeff')
# Input:  M_v,  a matrix over C(x) such that V' = M_v V, where V is a local integral basis at infinity;
#         u,  a polynomial in C[x], u = gcd(e_w, e_w'), where W' = M_w W, e_w = denom(M_w), W is a normalized integral basis;
#         tau,  an integer, tau = degree(T, x), where T = diag(x^tau_1, ..., x^tau_n) such that V = T W;
#         x,  a variable name.
# Output: integrable_reminder, ldeg, deg, e_v,
#         where integrable_reminder is a list of coefficient (row) vectors over C, mu, delta are integers, e_v = denom(M_v)
#         such that a basis of integrable HR reminder is represented by
#
#                           coeff. [ (x^i)/e_v) * V, i = ldeg, ..., deg]
#
#         where coeff belongs to integrable_reminder.
# Optional: the fifth and sixth arguments if presented are assigned
#                           integrand = [g1, g2, ...] which is a list of certificate vectors,
#                           rep_coeff = [s1, s2, ...] which is a Matrix over C and nops(rep_coeff) = nops(integrable_reminder),
#           such that   (integrand. si)' corresponds to the i-th term (coefficient vector) in integrable_reminder.
# Example: M_v := Matrix(2, 2, [[0, 1/x^3], [0, -2/x^3]]);
#          u := x^2;
#          tau := 0;
#          IntegrableReminder(M_v, u, tau, x);
#          # The result is
#          #  [Vector[row](6, [0, 0, 2, 1, 0, 0]), Vector[row](6, [0, 1, 0, 0, 0, 0]), Vector[row](6, [1, 0, 0, 0, 0, 0])], 0, 2, x^3
#          # which means the set of integrable HR reminders is generated by (2x/x^3)*v_1 + (x/x^3)*v2, v_2/x^3, v_1/x^3 if V = [v_1, v_2]
#          IntegrableReminder(M_v, u, tau, x, 'integrand', 'rep_coeff');
##########################################################################################################################################

IntegrableReminder := proc(M_v, u, tau, x, integrand, rep_coeff)
    local n, e_v, B, deg_B, mu, delta, mu2, delta2, integrand_list, integrable_list, denom_list, H, dH_coeff, \
    ee, integrable_list_numer, degree_list, deg, ldegree_list, ldeg, ee_v, deg_gap, reminder_list, reminder_space, \
    integrable_space, integrable_reminder, integrand_, mu_, delta_;
    n := LinearAlgebra:-Dimension(M_v)[1];
    e_v := mydenom(M_v, x);
    B := normal(e_v*M_v);
    deg_B := MatrixPolynomialAlgebra:-Degree(map(normal, B),x);

    mu := min(-tau, 0);
    delta := max(degree(e_v, x), deg_B) - 1;
    mu2 := min(-tau, ldegree(u, x));
    delta2 := max(degree(u, x), deg_B - degree(e_v, x) + degree(u, x));

    integrand_list := [seq((x^i/u)*LinearAlgebra:-IdentityMatrix(n), i = mu2..delta2)];
    integrable_list := [];
    denom_list := [];
    integrand_ := [];

    ##### obtain integrable_list and lcm of its denominators
    for H in integrand_list do
        dH_coeff := diff(H, x) + H.M_v;
        integrable_list := [op(integrable_list), dH_coeff];
        denom_list := [op(denom_list), mydenom(dH_coeff, x)];
        integrand_ := [op(integrand_), seq(LinearAlgebra:-Row(H,i), i = 1..n)]
    od:
    ee := lcm(op(denom_list), e_v);

    #### compute the degree and ldegee of integrable_list_numer
    integrable_list_numer := map( f -> simplify(ee*f), integrable_list);
    degree_list := map(f -> MatrixPolynomialAlgebra:-Degree(f, x), integrable_list_numer);
    deg := max(degree_list);
    ldegree_list := map(f -> MatrixPolynomialAlgebra:-Ldegree(f, x), integrable_list_numer);
    ldeg := min(ldegree_list);

    ee_v := normal(ee / gcd(ee, e_v));
    deg_gap := degree(ee_v);
    deg := max(deg, delta + deg_gap);
    ldeg := min(ldeg, mu + deg_gap);

    #### compute a (coefficient) basis of integrable HR reminder with respect to x^i*V, i = ldeg...deg
    reminder_list := [seq(ee_v*x^i*LinearAlgebra:-IdentityMatrix(n), i = mu..delta)];
    reminder_space := CoeffOfPolyMatrices(reminder_list, x, ldeg, deg);
    integrable_space := CoeffOfPolyMatrices(integrable_list_numer, x, ldeg, deg);
    integrable_reminder := LinearAlgebra:-IntersectionBasis([integrable_space, reminder_space]);

    if nargs = 6 then
        if integrable_reminder = [] then
            rep_coeff := 0;
            integrand := [];
        else
            rep_coeff := Representation_coeff(integrable_space, integrable_reminder);
            integrand := integrand_;
        fi;
    fi;

    #mu_ := (mu + deg_gap - ldeg)*n+1;
    #delta_ := (delta + deg_gap + 1)*n;
    #integrable_reminder := map( vec -> LinearAlgebra:-SubVector(vec, [mu_..delta_]), integrable_reminder);

    integrable_reminder, ldeg, deg, ee; ## basis (x^i/e_v)*V
end proc:


################################################################################################
## Export
## Name: GenerateBasis
## Calling sequence:
##                    GenerateBasis(V)
## Input:  V,  a set of linearly independent vectors.
## Output: A, m,  where A is an intertible matirx whose first m rows are vectors in V,
##                and the set of other rows forms a basis of the nullspace of V.
## Example: V := [Vector[row](6, [1, 0, 0, 0, 0, 0]), Vector[row](6, [0, 0, 2, 1, 0, 0]), Vector[row](6, [0, 1, 0, 0, 0, 0])];
##          GenerateBasis(V);
###############################################################################################

# GenerateBasis := proc(V)
#    local m, n, A, i, nullspace;
#
#    #### the vectors in V are linearly independent
#    ## construct a matrix A whose rows are vectors in V.
#    m := nops(V);
#    n := LinearAlgebra:-Dimension(V[1]);
#    A := Matrix(n, n);
#    for i from 1 to m do
#        A[i] := V[i];
#    od;
#
#    ## compute a basis of the Nullspace of A, i.e. a basis of the solution set {x | A x = 0 }
#    nullspace := LinearAlgebra:-NullSpace(A);
#    for i from m+1 to n do
#        A[i] := LinearAlgebra:-Transpose(nullspace[i-m]);
#    od;
#
#    A, m;
# end proc:

##############################################################################################################################
# Export
# Name: GenerateBasis
# Calling sequence:
#                    GenerateBasis(V)
# Input:  V,  a set of linearly independent vectors.
# Output: A, m,  where A is an intertible matirx whose first m rows are vectors in V,
#                and the set of other rows forms a basis of a complement of V, which are filled with 1 in appropriate places.
# Example: V := [Vector[row](6, [1, 0, 0, 0, 0, 0]), Vector[row](6, [0, 0, 2, 1, 0, 0]), Vector[row](6, [0, 1, 0, 0, 0, 0])];
#          GenerateBasis(V);
##############################################################################################################################

GenerateBasis := proc(V)
    local A, G, B, place, i, j, n, number_set, b, m;
    m := nops(V);
    n := LinearAlgebra:-Dimension(V[1]);
    A := Matrix(m, n);
    for i from 1 to m do
        A[i] := V[i];
    od;

#### perform Gaussian elimination ####
    #A := convert(k, Matrix);
    G := LinearAlgebra:-GaussianElimination(A);
    B := convert(G, Array);

#### find the place of the first nonzero element in each row of the matrix ####
    place := [];
    for i from 1 to m do
        j := ArrayTools:-SearchArray(B[i], 1, location = first);
        place := [op(place), j[1]];
    end do;
    #n := nops(k[1]);
    number_set := {seq(i, i = 1 .. n)};
    place := number_set minus convert(place, set);

#### put 1 on appropriate places ####
    for i in place do
        b := LinearAlgebra:-Transpose(convert(Vector(n, shape = unit[i]), Matrix));
        A := Matrix([[A], [b]]);
    end do;
    A, m;
end proc:


##########################################################################################################
# Export
# Name: ProjectiveComponent
# Calling sequence:
#                    ProjectiveComponent(x, A, m)
#                    ProjectiveComponent(x, A, m, 'y')
# Input:  x,  a vector over C;
#         A,  an invertible matrix over C.
# Output: x1, x2,  let V1, V2 be the vector space generated by the first m rows and the other rows and decompose x as
#                               x = x1 + x2
#                  where x1 in V1 and x2 in V2;
# Example: x := Vector[row](6, [0, 0, -4/3, -2/3, 0, 0]);
#          A := Matrix(6, 6, [[1, 0, 0, 0, 0, 0], [0, 0, 2, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, -1/2, 1, 0, 0]]);
#          m := 3;
#          ProjectiveComponent(x, A, m);
#          The result is Vector[row](6, [0, 0, -4/3, -2/3, 0, 0]), Vector[row](6, [0, 0, 0, 0, 0, 0])
# Optional: the fourth arguement if presented are assigened,
#                  y = [y1, y2]
#           such that x1 = A^T.y1 and x2 = A^T.y2.
###########################################################################################################

ProjectiveComponent := proc(x, A, m, y_)
    local B, b, y, y1, y2, x1, x2, i, n;
    #### compute the unique solution y of A^T.y = x^T
    B := LinearAlgebra:-Transpose(A);
    b := LinearAlgebra:-Transpose(x);
    y := LinearAlgebra:-LinearSolve(B, b);

    #### decompose x = x_1 + x_2 with x_1 in V, x_2 in the nullspace of V
    n := LinearAlgebra:-Dimension(A)[1];
    y1 := ArrayTools:-Concatenate(1, y[1..m], LinearAlgebra:-ZeroVector(n-m));
    y2 := ArrayTools:-Concatenate(1, LinearAlgebra:-ZeroVector(m), y[m+1..n]);
    x1 := LinearAlgebra:-Transpose(B.y1);
    x2 := LinearAlgebra:-Transpose(B.y2);

    if nargs = 4 then
        y_ := [y1, y2];
    fi;

    x1, x2;
end proc:



##############################################################################################################
# Export
# Name: myReverseVector
# Calling sequence:
#                    myReverseVector(v, n)
# Input:  v,  a vector over C;
#         n,  a nonzero natural number.
# Output: v_reverse,  a vector over C such that v_reverse = (v_s, ..., v_1)
#                     where v = (v_1, ..., v_s) with v_i in C^{1*n}
# Example: v := Vector[row](6, [1, 0, -4/3, -2/3, 0, 0]);
#          n := 2;
#          myReverseVector(v, n);
#          # The result is Vector[row](6, [0, 0, -4/3, -2/3, 1, 0]).
####################################I##################################################################################

myReverseVector := proc(v, n);
    local v_list, v_reverse;
    v_list := convert(v, list);
    v_reverse := ListTools:-Reverse([ListTools:-    LengthSplit(v_list, n)]);
    v_reverse := Vector[row](ListTools:-FlattenOnce(v_reverse));
end proc:


##############################################################################################################
# Export
# Name: myReverseMatrix
# Calling sequence:
#                    myReverseMatrix(A, n)
# Input:  A,  a matrix in C^{m*s};
#         n,  a nonzero natural number.
# Output: A_reverse,  a matrix in C^{m*n} such that A_reverse =  v_reverse = (v_k, ..., v_1)
#                     where v = (v_1, ..., v_k) with v_i in C^{m*n} and k = s/n;
# Example: A := Matrix(4, 4, [[0, 0, -1/3, 1], [-1/3, 1, 0, 0], [0, 0, 3, 1], [3, 1, 0, 0]]);
#          n := 2;
#          myReverseMatrix(A, n);
####################################I##################################################################################

myReverseMatrix := proc(A, n);
    local d, A_reverse, i;
    d := LinearAlgebra:-Dimension(A);
    A_reverse := Matrix(d[1], d[2]);
    for i from 1 to d[1] do
        A_reverse[i] := myReverseVector(A[i], n);
    od;
    A_reverse;
end proc:


########################################################################################################################
# Export
# Name: AdditiveDecomposition
# Calling sequence:
#                    AdditiveDecomposition(f, basis, Dx, x, L)
# Input:  f,  an element in C(x)[Dx]/<L>;
#         basis,  basis = [W, degree], where W is a normalized integral basis of C(x)[Dx]/<L> and degree= [-val_infty(W[i])];
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: [g, [P1, W], [Q1, V], h],
#         where g, h in C(x)[Dx]/<L>, P1, Q1 are list of coefficients in C(x)^n, W is a normalized integral basis and
#         V is a local integral basis at infinity such that
#                    f = g' + h    with    h = P1 * W + Q1 * V
#         and f is integrable if and only if h = 0.
# Example: f := -1-2/ x^2 + (-2+3*x^2 -3*x^4)*Dx/x;
#          L := x^3*Dx^2+(2+3*x^2)*Dx;
#          basis := [[x^3*Dx, 1], [0, 0]];
#          AdditiveDecomposition(f, basis, Dx, x, L);
####################################I###################################################################################

AdditiveDecomposition := proc(f, basis, Dx, x, L, A)
    local g, h1, h2, h, W, val_infty, n, T, V, M_w, e_w, M_v, tau, u, int_basis, mu_, delta_, ee, Q, h2_numer, \
    linear_basis, c, g_rep, m, h21, h22, W_vector, V_vector, Q1;

    g, h1, h2, h := op(HR(f, basis, Dx, x, L));
    W := basis[1];

    val_infty := - basis[2];
    n := nops(val_infty);
    T := LinearAlgebra:-DiagonalMatrix([seq(x^val_infty[i], i = 1..n)]); ## V = TW
    V := [seq(W[i]*x^val_infty[i], i=  1..n)];

    M_w := BasisMatrix(W, Dx, x, L);
    e_w := mydenom(M_w, x);
    M_v := BasisMatrix(V, Dx, x, L);
    #e_v := mydenom(M_w, x);

    tau := max(val_infty);
    u := gcd(e_w, diff(e_w, x));
    int_basis, mu_, delta_, ee:= IntegrableReminder(M_v, u, tau, x, 'integrand', 'int_rep');

    #### The only integrable HR reminder is zero
    if evalb(int_basis = []) = true then
        return [g, h1, h2, h];

    #### There exists a nonzero integrable HR reminder
    else
        Q := ee*convert(h2[1], Matrix);
        h2_numer := op(CoeffOfPolyMatrices([Q], x, mu_, delta_));
        linear_basis, m := GenerateBasis(map(v -> myReverseVector(v, n), int_basis));
        h21, h22 := ProjectiveComponent(myReverseVector(h2_numer, n), linear_basis, m, 'rep_h');
        c := rep_h[1](1..nops(int_basis)); ## integralbe part,  h21 = linear_basis.rep_h[1]
        h22 := myReverseVector(h22, n); ## reminder


        #### compte a certificate g of the additive decomposition
        V_vector := convert(V, Vector);
        g_rep := int_rep.c;
        g := g + add((integrand[i].V_vector)*g_rep[i], i = 1..nops(integrand));

        #### compte a reminder h of the additive decomposition
        h22 := simplify(FromCoeffToPolyVector(h22, mu_, 'x', n)/ee);

        h := simplify(Vector[row](h1[1]).Vector[column](W) + h22.V_vector);

        Q1 := convert(h22, list);
        return [g, h1, [Q1, V], h];
    fi;
end proc:


########################################################################################################################
# Export
# Name: CreativeTelescoping
# Calling sequence:
#                    CreativeTelescoping(f, ann, basis, Der_x, Der_t)
#                    CreativeTelescoping(f, ann, basis, Der_x, Der_t, 'cert')
# Input:  f,  an operator in C(x, t)[Dx, Dt];
#         ann,  ann = [L, P] where L in C(x,t)[Dx] and P = c*Dt - U_t with c in C(x,t) and U_t in C(x, t)[Dx];
#         Der_x, Der_x = [Dx, x], where Dx is a differential operator with repect to x and x is a variable name;
#         Der_t, Der_t = [Dt, t], where Dt is a differential operator with repect to t and t is a variable name.
# Output: L, where L in C(t)[Dt] and g in C(x)[Dx, Dt]/ann such that
#                    L(f) = Dx(g)
#         and L is of minimal order.
# Optional: The optional argument is assigned cert = g.
# Example: f := 1;
#          ann := [Dx^2 + 4*x*Dx +(2+t^2+4*x^2), Dt - x/t*Dx - 2*x^2/t];
#          basis := [[Dx + 2*x, 1], [0, 0]];
#          CreativeTelescoping(f, ann, basis, [Dx, x], [Dt, t]);
####################################I###################################################################################

CreativeTelescoping := proc(f_, ann, basis, Der_x, Der_t, cert)
     local n, rem_list, g, h, f, r, polys_list, j, sol, telescoper, L, P, Dx, x, Dt, t, i, df;
     L := ann[1];
     P := ann[2];
     Dx, x := op(Der_x);
     Dt, t := op(Der_t);
     n := degree(L, Dx);
     f := StandardForm(f_, ann, Der_x, Der_t);
     rem_list := [AdditiveDecomposition(f, basis, Dx, x, L)];
     g := rem_list[1][1];
     h := rem_list[1][4];

     ##### check if f is integrable ####
     if h = 0 then
          if nargs = 6 then
              cert := g;
          fi;
          return 1;
     fi;
     df := f;
     while true do
         df := DiffOperator2(df, ann, t, Der_x, Der_t);
         rem_list := [op(rem_list), AdditiveDecomposition(df, basis, Dx, x, L)];
         printf("check order %d\n", nops(rem_list)-1);

         #### check if remainders are linearly dependent ####
         r := nops(rem_list);
         polys_list := [];
         for j from 1 to n do
             polys_list := [op(polys_list), [seq(rem_list[i][2][1][j], i = 1..r)],[seq(rem_list[i][3][1][j], i = 1..r)]];
         od;
         polys_list;

         sol := LinearRelation:-FindLinearRelation3(polys_list, x);

         if sol <> []  then
             telescoper := add(sol[i]*Dt^(i-1), i = 1..r);
             if nargs = 6 then
                 cert := add(sol[i]*rem_list[i][1], i = 1..r);
             fi;
             return telescoper;
         fi;
     od;

end proc:


########################################################################################################################
# Export
# Name: VerifyTelescoper
# Calling sequence:
#                    VerifyTelescoper(T, f, g, ann, Der_x, Der_t)
# Input:  T, an operator in C(t)[Dt];
#         f, g, two operators in C(t, x)[Dx]/<L>;
#         ann,  ann = [L, P] where L in C(x,t)[Dx] and P = c*Dt - U_t with c in C(x,t) and U_t in C(x, t)[Dx];
#         Der_x, Der_x = [Dx, x], where Dx is a differential operator with repect to x and x is a variable name;
#         Der_t, Der_t = [Dt, t], where Dt is a differential operator with repect to t and t is a variable name.
# Output: true, if  Lf = g';
#         false, otherwise.
# Example: CT:=-3*(t^3 - 2)/(2*t) + Dt;
#          f_:=1; ## sqrt(t-2x)*exp(t^2*x);
#          g:=-3*(t^3 - 2)*(x/t^2 - 1/(2*t^4))/(2*t*x) + (2*x^2/t - 3*x/t^3 + (-3*t^3 + 6)/(4*t^5))/x;
#          ann := [Dx - (t^3 - 2*t^2*x - 1)/(t - 2*x), Dt - (4*t^2*x - 8*t*x^2 + 1)/(2*t - 4*x)];
#          VerifyTelescoper(CT, f, g, ann, [Dx, x], [Dt, t]);
####################################I###################################################################################

VerifyTelescoper := proc(T, f, g, ann, Der_x, Der_t)
    local L, P, Dx, x, Dt, t, T_coeff, r, Lf;
    L := ann[1];
    P := ann[2];
    Dx, x:= op(Der_x);
    Dt, t:= op(Der_t);

    r := degree(T, Dt);
    T_coeff :=[seq(coeff(T, Dt, i), i = 0..r)];
    Lf := T_coeff[1]*f + add(T_coeff[i+1]*DiffOperator2(f, ann, t, Der_x, Der_t, i), i = 1..r) ;

    Testzero(Lf - DiffOperator(g,Dx,x,L));
end proc;



########################################################################################################################
# Export
# Name: Verify_HR
# Calling sequence:
#                    Verify_HR(f, g, h, Dx, x, L)
# Input:  f, g, h,  three operators in C(x)[Dx]/<L>;
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: true, if  f = g' + h,
#         false, otherwise.
####################################I###################################################################################

Verify_HR := proc(f, g, h, Dx, x, L)
    local r;
    r := simplify(f - DiffOperator(g,Dx,x,L) - h);
    Testzero(r);
end proc;


########################################################################################################################
# Export
# Name: Verify_HR_step_dfinite
# Calling sequence:
#                    Verify_HR_step(f, g_coeff, h_coeff, Dx, x, L)
# Input:  f,  an operator in C(x)[Dx]/<L>;
#         g_coeff,  a vector in C(x)^n, representing the coefficients of g with respect to an integral basis W;
#         h_coeff,  a vector in C(x)^n, representing the coefficients of h with respect to an integral basis W;
#         Dx, name, a differential operator with repect to x;
#         x,  a variable name;
#         L,  a linear differential operator in C(x)[Dx].
# Output: true, if  f = g' + h, i.e., f = (g_coeff.W)' + (h_coeff.W);
#         false, otherwise.
# Example: f := -1-2/ x^2 + (-2+3*x^2 -3*x^4)*Dx/x/(x+2)^2;
#          L := x^3*Dx^2+(2+3*x^2)*Dx;
#          W := [1, x^3*Dx];
#          g_coeff, h_coeff, W := op(HR_step_dfinite(f, W, Dx, x, L));
#          Verify_HR_step_dfinite(f, g_coeff, h_coeff, Dx, x, L);
####################################I###################################################################################

Verify_HR_step_dfinite := proc(f, g_coeff, h_coeff, Dx, x, L)
    local g, h;
    g := FromCoeffToOperator(g_coeff, W);
    h := FromCoeffToOperator(h_coeff, W);
    Testzero(f - DiffOperator(g,Dx,x,L) - h);
end proc:

end module:


################################################################################
## Copyright (c) January 2013, NCSU. All rights reserved.
## Author: Shaoshi Chen <schen@amss.ac.cn>
## Load the modules:
##  Decomposition.mm, Division.mm, HyperexpReduction.mm, List.mm, Hyperexp.mm
##
## Modified on April 12, 2013 (+ a code to add rational functions)
################################################################################


   LinearRelation := module()
    description "Find linear dependency between polynomials";

    export
          FindLinearRelation,
          FindLinearRelation1,
          FindLinearRelation2,
          FindLinearRelation3;
    local
          FindLinearRelationOneList,
          IsZeroVector,
          IsZeroList,
          LowerBoundForRank;

    option package;

###############################################
## Name: FindLinearRelation
##
##           FindLinearRelation(pL, vL, y)
## Input: pL, vL, two same-size lists of polynomials;
##        y, a variable name.
## Output: cL, a list of constants (free of y) such that
##
##         add(pL[i]*cL[i], i=1..n) =0
##                   and
##         add(vL[i]*cL[i], i=1..n) =0
##
##              where n = nops(pL).
################################################

FindLinearRelation :=proc(pL, vL, y)

    local cL, tt, np, pp, clp, gm, MM, clv, pv, sys, vars, i, j, m, p, r, sol;

    cL := table([]);
    np := nops(pL);

    #### Generate a matrix of coefficients
    vars := [seq(cL[i], i=1..np)];
    pp   := collect(numer(add(cL[i]*pL[i], i=1..np)), y);
    pv   := collect(numer(add(cL[i]*vL[i], i=1..np)), y);


    clp  := convert(PolynomialTools:-CoefficientList(pp, y), set) minus {0};
    clv  := convert(PolynomialTools:-CoefficientList(pv, y), set) minus {0};
    sys  := clp union clv;
    gm   := LinearAlgebra:-GenerateMatrix(sys, vars);
    if IsZeroVector(gm[2]) then
       MM := gm[1];
    else
       return([]);
    end if;

    #### Find linear dependency
    for j from 1 to 3 do
      m := rand(6..100):
      p := ithprime(m()):
      r := LowerBoundForRank(MM, p):
      if r = np then
         return([]):
      end if:
    end do:
    ###tt := time():
    sol := LinearAlgebra:-NullSpace(MM);

    ####tt := time()-tt; print(tt);


    if nops(sol) =0 then
       return([]);
    else
       convert(sol[1], list);
    end if;

end proc;


FindLinearRelation1 :=proc(pL, vL, y)

    local cL, cpt, cvt, tt, np, pp, clp, gm, MM, clv, pv, sys, vars, i, j, m, p, r, sol;

    cL := table([]);
    np := nops(pL);

    #### Generate a matrix of coefficients
    vars := [seq(cL[i], i=1..np)];
    pp   := collect(numer(add(cL[i]*pL[i], i=1..np)), y);
    pv   := collect(numer(add(cL[i]*vL[i], i=1..np)), y);

    cpt := content(pp, [op(vars), y], 'pp');
    cvt := content(pv, [op(vars), y], 'pv');
    print([cpt, cvt]);


    clp  := convert(PolynomialTools:-CoefficientList(pp, y), set) minus {0};
    clv  := convert(PolynomialTools:-CoefficientList(pv, y), set) minus {0};
    sys  := clp union clv;
    gm   := LinearAlgebra:-GenerateMatrix(sys, vars);
    if IsZeroVector(gm[2]) then
       MM := gm[1];
    else
       return([]);
    end if;

    #### Find linear dependency
    for j from 1 to 2 do
      m := rand(6..100):
      p := ithprime(m()):
      r := LowerBoundForRank(MM, p):
      if r = np then
         return([]):
      end if:
    end do:
    tt := time():
    sol := LinearAlgebra:-NullSpace(MM);

    tt := time()-tt; print(tt);


    if nops(sol) =0 then
       return([]);
    else
       convert(sol[1], list);
    end if;

end proc;



FindLinearRelationOneList :=proc(pL, vars, y)

    local cL, cpL, ppL, np, pp, poly, clp, gm, MM, sys,  i, j, m, p, r, sol;


    np := nops(pL);
    cpL := table([]);
    ppL := table([]);

    ### Find the contents of pL
    for i from 1 to np do
        cpL[i] := content(pL[i], y, 'pp');
        ppL[i] := pp;
    end do;


    #### Generate a matrix of coefficients
    poly   := collect(normal(add(vars[i]*ppL[i], i=1..np)), y);
    sys  := convert(PolynomialTools:-CoefficientList(poly, y), set) minus {0};
    gm   := LinearAlgebra:-GenerateMatrix(sys, vars);
    if IsZeroVector(gm[2]) then
       MM := gm[1];
    else
       return([]);
    end if;

    #### Find linear dependency
    for j from 1 to 2 do
      m := rand(6..100):
      p := ithprime(m()):
      r := LowerBoundForRank(MM, p):
      if r = np then
         return([]):
      end if:
    end do:

    ### sol := LinearAlgebra:-NullSpace(MM);
    sol := SolveTools:-Linear(sys, vars);
    if IsZeroList(eval(vars, sol)) then
       return([]);
    else
       ## convert(sol[1], list);
       eval([seq(vars[i]/cpL[i], i=1..np)], sol);
    end if;
end proc;


FindLinearRelation2 := proc(pLL, vars, y)

    local sol, nvars, npLL, i, j, tt, k, pvars, idts, pLLs, ps, poly, su, sol2;


   ## pLL is a list of lists of polynomials

      npLL := nops(pLL);
      if npLL = 0 then
         return(vars);
      else
         tt := time():
         sol := FindLinearRelationOneList(pLL[1], vars, y);
         print(time_1);
         tt := time()-tt; print(tt);

         ### find the free variables
         nvars := [];
         pvars := [];
         idts := indets(sol);
         for i from 1 to nops(vars) do
             if has(idts, vars[i]) then
                nvars := [op(nvars), vars[i]];
                pvars := [op(pvars), i];
             end if;
         end do;
    end if;


         ### update the other lists in pLL
         pLLs := [];
         for i from 2 to npLL do
             ps := [];
             for j from 1 to nops(pvars) do
                 poly := 0;
                 for k from 1 to nops(pLL[i]) do
                     poly := normal(poly + coeff(sol[k], nvars[j], 1)*pLL[i][k]);
                 end do;
                 ps := [op(ps), poly];
             end do;
             pLLs := [op(pLLs), ps];
         end do;

tt := time():
        su := FindLinearRelation2(pLLs, nvars, y);
print(time_2);
tt := time()-tt;
print(tt);

        if nops(su)=0 then
           return([]);
        else
        sol2 := {seq(nvars[i]=su[i], i=1..nops(nvars))};
        eval(sol, sol2);
        end if;

end proc;



##################################################################################
## Name: FindLinearRelation3
##
##           FindLinearRelation3(pL, y)
## Input: ppL, a list of the list of polynomials of the same size;
##        y, a variable name.
## Output: cL, a list of constants (free of y) such that
##
##         add(ppL[j][i]*cL[i], i=1..n) =0 for all j = 1..s
##
##              where n = nops(ppL[1]), s = nops(ppL).
## Make a small modifiction of FindLinearRelation. (by Lixin Du <lixin.du@jku.at>)
##################################################################################

FindLinearRelation3 :=proc(ppL, y)

    local cL, tt, np, pp, clp, gm, MM, pL, sys, vars, i, j, m, p, r, sol;

    cL := table([]);
    np := nops(ppL[1]);


    #### Generate a matrix of coefficients
    vars := [seq(cL[i], i=1..np)];
    sys := {};
    for pL in ppL do
        pp   := collect(numer(add(cL[i]*pL[i], i=1..np)), y);

        clp  := convert(PolynomialTools:-CoefficientList(pp, y), set) minus {0};
        sys  := sys union clp;
    od;
    gm   := LinearAlgebra:-GenerateMatrix(sys, vars);
    if IsZeroVector(gm[2]) then
       MM := gm[1];
    else
       return([]);
    end if;

    #### Find linear dependency
    for j from 1 to 3 do
      m := rand(6..100):
      p := ithprime(m()):
      r := LowerBoundForRank(MM, p):
      if r = np then
         return([]):
      end if:
    end do:
    ###tt := time():
    sol := LinearAlgebra:-NullSpace(MM);

    ####tt := time()-tt; print(tt);


    if nops(sol) =0 then
       return([]);
    else
       convert(sol[1], list);
    end if;

end proc:


###############################################################

  IsZeroVector :=proc(v)
    local i, vs;
    vs := convert(v, list);
    for i from 1 to nops(vs) do
        if not Testzero(vs[i]) then
           return(false)
        end if;
    end do;
    true;
  end proc;

IsZeroList :=proc(v)
    local i;
    for i from 1 to nops(v) do
        if not Testzero(v[i]) then
           return(false)
        end if;
    end do;
    true;
  end proc;

  ####################################################################
  # This code is from OreTools_ModularGCRDLCLM
  # Name: LowerBoundForRank
  # Calling sequence:
  #                   LowerBoundForRank(M, p)
  #
  # Input: M, A matrix with entries being multivariate polynomials
  #           over p:
  #        p, a prime:
  # Output: b, a nonnegative integer less than or
  #            equal to the rank of M.
  ####################################################################

   LowerBoundForRank := proc(M, p)
        local rn, cn, vars, g, e, N, i, j, en, s, b, de, dei, MM:

        #------------------------------
        # 1. Collect info about matrix
        #------------------------------

        rn := op(1, M)[1]:
        cn := op(1, M)[2]:
        vars := [op(indets(M))]:


        #---------------------------------------
        # Calculate rowwise common denominators
        #---------------------------------------

        de := []:
        for i from 1 to rn do
            dei := []:
            for j from 1 to cn do
                dei := [op(dei), denom(M[i,j])]:
            end do:
            de := [op(de), Lcm(op(dei)) mod p]:
        end do:

        MM := Matrix(rn, cn):
        for i from 1 to rn do
            for j from 1 to cn do
                MM[i,j] := Normal(de[i]*M[i,j]) mod p:
            end do:
        end do:


        #----------------------------------
        # 2. Choose two evaluation points
        #----------------------------------

        g := rand(1..p-1):
        e := [seq(g(), i=1..nops(vars))]:
        s := {seq(vars[i]=e[i], i=1..nops(vars))}:

        #---------------
        # 3. Evaluation
        #---------------

        N := Matrix(rn, cn):
        for i from 1 to rn do
                for j from 1 to cn do
                    N[i, j] := Expand(subs(s, MM[i, j])) mod p:
                end do:
        end do:

        #--------------------
        # 4. Compute rank(N)
        #--------------------

        LinearAlgebra:-Modular:-RowReduce(p, N, rn, cn, cn, 0,
                      0, b, 0, 0, false):
        return(b):

   end proc:

end module:
