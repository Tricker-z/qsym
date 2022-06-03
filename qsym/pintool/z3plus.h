/*
 * z3plus.h
 * rainoftime@gmail.com
 */

#ifndef Z3PLUS_H_
#define Z3PLUS_H_
#include <vector>
#include <set>
#include <future>
#include <map>
#include <iostream>
#include <memory>
#include <set>
#include <vector>
#include <algorithm>
#include "z3++.h"
#include "z3.h"
using namespace z3;
/*
 * We provide the following APIs
 *  - get_expr_vars(exp, vars)
 *      get all variables of exp and store in vars
 *  - get_vars_differenct(vars_a, vars_b)
 *      set differences of vars_a and vars_b
 *  - get_k_modles(exp, k)
 *      use the solver to get k models
 *  - get_abstract_interval(pre_cond, query)
 *      get the interval of query, under the condition pre_cond
 *  - get_abstract_interval_as_expr
 *      get the result as a z3 expr
 *  - do_constant_propagation(exp)
 *      use cp to simplify exp
 *  - check_model
 *
 *  - is_sat_under_partial_model
 */

bool get_expr_vars(expr& exp, expr_vector& vars) {
    // TODO: test the efficiency of this function
    try {
        auto& ctx = exp.ctx();
        auto compare_func = [](const z3::expr& a, const z3::expr& b) {
            Z3_symbol sym_a = a.decl().name();
            Z3_symbol sym_b = b.decl().name();
            return sym_a < sym_b;
        };
        std::set<z3::expr, decltype(compare_func)> syms(compare_func);
        std::function<void(const z3::expr&)> recur = [&recur, &syms, &ctx](
                const z3::expr& e) {
            assert(Z3_is_app(ctx, e));
            auto app = Z3_to_app(ctx, e);
            unsigned n_args = Z3_get_app_num_args(ctx, app);

            auto fdecl = Z3_get_app_decl(ctx, app);
            if (n_args == 0 && Z3_get_decl_kind(ctx, fdecl) == Z3_OP_UNINTERPRETED)
                syms.insert(e);

            for (unsigned i = 0; i < n_args; ++i) {
                z3::expr arg(ctx, Z3_get_app_arg(ctx, app, i));
                recur(arg);
            }
        };
        recur(exp);
        // if the return type is std::vector<z3::expr>
        //return std::vector<z3::expr>(syms.begin(), syms.end());;
        for (auto& i : syms) {
            vars.push_back(i);
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return false;
    }
    return true;
}
// note that we assume vars_a and vars_b consist of purely variables.
expr_vector get_vars_difference(expr_vector& vars_a, expr_vector& vars_b) {
    expr_vector ret(vars_a.ctx());
    try {
        for (unsigned i = 0; i < vars_a.size(); i++) {
            bool is_in_diff = true;
            Z3_symbol sym_i = vars_a[i].decl().name();
            for (unsigned j = 0; j < vars_b.size(); j++) {
                if (sym_i == vars_b[j].decl().name()) { is_in_diff = false; }
            }
            if (is_in_diff) { ret.push_back(vars_a[i]); }
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return ret;
    }
    return ret;
}
// TODO: store the models
void get_k_models(z3::expr& exp, int k) {
    z3::context& ctx = exp.ctx();
    z3::solver solver(ctx);
    solver.add(exp);
    while (solver.check() == z3::sat && k >= 1) {
        std::cout << solver << std::endl;
        // get model
        z3::model m = solver.get_model();
        z3::expr_vector args(ctx);
        for (unsigned i = 0; i < m.size(); i++) {
            // get z3 variable
            z3::func_decl z3Variable = m[i];
            std::string varName = z3Variable.name().str();
            z3::expr exp = m.get_const_interp(z3Variable);
            unsigned bvSize = exp.get_sort().bv_size();
            int value = m.eval(exp).get_numeral_int();
            // std::string svalue = Z3_get_numeral_string(ctx, exp);
            // uniq result
            if (exp.get_sort().is_bv()) {
                //args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(svalue.c_str(), bvSize));
                args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(value, bvSize));
            }
        }
        // block current model
        solver.add(mk_or(args));
        k--;
    }
}

std::pair<int, int> get_abstract_interval(expr& pre_cond, expr& query, int timeout) {
    // TODO: should we return an Expr or a domain value(like [a, b])
    z3::context &c = pre_cond.ctx();
    std::pair<int, int> ret(INT_MIN, INT_MAX);
    z3::optimize opt1(c);
    z3::optimize opt2(c);
    z3::params p(c);
    p.set("priority", c.str_symbol("pareto"));
    z3::set_param("smt.timeout", timeout);
    //p.set("timeout", Timeout); TODO: it seems we cannot set timeout directly to opt
    opt1.set(p); opt2.set(p);
    opt1.add(pre_cond);
    z3::optimize::handle h1 = opt1.maximize(query);
    opt2.add(pre_cond);
    z3::optimize::handle h2 = opt2.minimize(query);
    try {
        if (opt1.check() == z3::sat) {
            //std::cout << __LINE__ << std::endl;
            //std::cout << opt1.get_model() << std::endl;
            ret.second = opt1.lower(h1).get_numeral_int();
            //std::cout << __LINE__ << std::endl;
        }
    } catch (z3::exception &ex) {
        std::cout << ex << std::endl;
    }
    try {
        if (opt2.check() == z3::sat) {
            //std::cout << __LINE__ << std::endl;
            //std::cout << opt1.upper(h2) << std::endl;
            ret.first = opt2.upper(h2).get_numeral_int();
            //std::cout << __LINE__ << std::endl;
        }
    } catch (z3::exception &ex) {
        std::cout << ex << std::endl;
    }
    return ret;
}

void get_abstract_interval_as_expr(expr& pre_cond, expr& query, expr_vector& res, int timeout) {
    context &Ctx = pre_cond.ctx();
    params Param(Ctx);
    Param.set("priority", Ctx.str_symbol("pareto"));
    set_param("smt.timeout", timeout);
    //p.set("timeout", Timeout); TODO: it seems we cannot set timeout directly to opt
    optimize UpperFinder(Ctx);
    optimize LowerFinder(Ctx);
    UpperFinder.set(Param); LowerFinder.set(Param);
    UpperFinder.add(pre_cond);
    optimize::handle UpperGoal = UpperFinder.maximize(query);
    LowerFinder.add(pre_cond);
    optimize::handle LowerGoal = LowerFinder.minimize(query);
    try {
        if (LowerFinder.check() == z3::sat) {
            //std::cout << "Find lower success\n";
            res.push_back(LowerFinder.upper(LowerGoal));
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }
    try {
        if (UpperFinder.check() == z3::sat) {
            //std::cout << "Find upper success\n";
            res.push_back(UpperFinder.lower(UpperGoal));
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }
}
/*
 *
 *  context ctx;
    expr x = ctx.bv_const("x", 32);
    expr y = ctx.bv_const("y", 32);

    expr pre_cond = x <= 9 && x >= 5 && y >= 3 && y <= 10;

    expr_vector query(ctx);
    query.push_back(x);
    query.push_back(y);

    expr_vector res_x(ctx);
    expr_vector res_y(ctx);
    std::vector<expr_vector> multi_res;
    multi_res.push_back(res_x); multi_res.push_back(res_y);

    get_abstract_interval_as_expr_multi_obj(pre_cond, query, multi_res);
 */
// experimental; only works for z3 version > 4.7?
void get_abstract_interval_as_expr_multi_obj(expr& pre_cond, expr_vector& query,
        std::vector<expr_vector>& res, int timeout) {
    context& Ctx = pre_cond.ctx();

    params Param(Ctx);
    Param.set("priority", Ctx.str_symbol("box"));
    set_param("smt.timeout", (int)timeout);
    //TODO: it seems we cannot set timeout directly to opt.. Maybe the new version of z3 is OK..
    //Param.set("timeout", (unsigned)timeout);
    optimize Opt(Ctx);
    Opt.set(Param); Opt.add(pre_cond);

    std::vector<std::pair<optimize::handle, optimize::handle>> goals;
    for (unsigned i = 0; i < query.size(); i++) {
        goals.push_back(std::make_pair(Opt.minimize(query[i]), Opt.maximize(query[i])));
    }
    try {
        if (Opt.check() == z3::sat) {
            for (unsigned i = 0; i < query.size(); i++) {
                expr upper = Opt.lower(goals[i].second);

                res[i].push_back(Opt.upper(goals[i].first));
                res[i].push_back(Opt.lower(goals[i].second));
            }
        }
    } catch(z3::exception &Ex) {
        //es.push_back(Ctx.bool_val(false));
    }
}


void get_abstract_interval_as_expr_with_qsmt(expr& pre_cond, expr& query, expr_vector& res, int timeout) {
    context& ctx = pre_cond.ctx();
    params p(ctx);
    p.set("timeout", (unsigned)timeout);
    solver sol_min = tactic(ctx, "ufbv").mk_solver();
    sol_min.set(p);
    solver sol_max = tactic(ctx, "ufbv").mk_solver();
    sol_max.set(p);

    // find min
    expr query_min = ctx.bv_const("rot_min", query.get_sort().bv_size());
    Z3_ast from[] = { query };
    Z3_ast to[] = { query_min };
    expr repl_min(ctx);
    repl_min = to_expr(ctx, Z3_substitute(ctx, pre_cond, 1, from, to));

    expr qsmt_min = pre_cond && forall(query_min, implies(repl_min, query_min >= query));
    sol_min.add(qsmt_min);
    if (sol_min.check() == sat) {
        model m = sol_min.get_model();
        expr lower = m.eval(query);
        res.push_back(lower);
    } else {
        res.push_back(ctx.bool_val(false));
    }

    // find max
    expr query_max = ctx.bv_const("rot_max", query.get_sort().bv_size());
    Z3_ast from_x[] = { query };
    Z3_ast to_x[] = { query_max };
    expr repl_max(ctx);
    repl_max = to_expr(ctx, Z3_substitute(ctx, pre_cond, 1, from_x, to_x));
    expr qsmt_max = pre_cond && forall(query_max, implies(repl_max, query_max <= query));
    sol_max.add(qsmt_max);
    if (sol_max.check() == sat) {
        model m = sol_max.get_model();
        expr upper = m.eval(query);
        res.push_back(upper);
    } else {
        res.push_back(ctx.bool_val(false));
    }
}


expr do_constant_propagation(expr& to_simp) {
    goal gg(to_simp.ctx());
    gg.add(to_simp);
    tactic cp = tactic(to_simp.ctx(), "propagate-values");
    return cp.apply(gg)[0].as_expr();
}

bool check_model_misc(expr& exp, context &ctx, vector<func_decl>& decls, vector<int>& candidate) {
    model cur_model(ctx);

    // initialize the model with candidate
    for (unsigned i = 0; i < decls.size(); i++) {
        // TODO: decide the bit-vector size
        expr var_i = ctx.bv_val(candidate[i], 8);
        cur_model.add_const_interp(decls[i], var_i);
    }
    // check if exp is satisfied by cur_model
    expr xx = cur_model.eval(exp);
    if (xx.is_true()) { 
        return true; 
    }
    else { 
        return false; 
    }
}

bool check_model_with_mutate(expr& exp) {
    expr_vector vars(exp.ctx());

    // get vars
    get_expr_vars(exp, vars);
    unsigned var_num = vars.size();

    // get decls
    vector<func_decl> decls;
    for (unsigned i = 0; i < var_num; i++) {
        decls.push_back(vars[i].decl());
    }

    // get candidate
    // TODO: generate candidate automatically
    // e.g., sampling on a polytope
    vector<int> candidate;
    for (unsigned i = 0; i < var_num; i++) {
        candidate.push_back(0);
    }

    // check the model
    bool res = check_model_misc(exp, exp.ctx(), decls, candidate);
    return res;
}


/*
 *\p  exp: the cnts
 *\p  m:   the full model
 *\p  donot_cared_vars: the don't cared vars
 *
 * For example
 * expr G =  a == 6 || (b + c == 4 && c - d == 2);
 *
 * A partial model is [a = 6, b = any, c = any]
 */
bool sat_under_partial_model(expr& exp, model& m, expr_vector& donot_cared_vars) {
    model partial_model(exp.ctx());

    unsigned num_constants = m.num_consts();
    for (unsigned i = 0; i < num_constants; i++) {
        z3::func_decl decl = m.get_const_decl(i);
        bool add_to_partial_model = true;
        for (unsigned j = 0; j < donot_cared_vars.size(); j++) {
            if (donot_cared_vars[j].decl().name() == decl.name()) {
                add_to_partial_model = false;
                break;
            }
        }
        if (add_to_partial_model) {
            z3::expr val_e = m.get_const_interp(decl);
            partial_model.add_const_interp(decl, val_e);
        }
    }
    // check if exp is satisfied by cur_model
    if (partial_model.eval(exp, true).is_true()) { return true; }
    else { return false; }
}



model& get_random_model(expr& exp, model& m, expr& var_s, int v) {
    model random_model(exp.ctx());
    unsigned num_constants = m.num_consts();

    //first, fix other variables
    for (unsigned i = 0; i <  num_constants; i++) {
        // TODO: decide the bit-vector size
        z3::func_decl decl = m.get_const_decl(i);
        z3::expr val_e = m.get_const_interp(decl);
        if (decl.name() != var_s.decl().name()) {
            random_model.add_const_interp(decl, val_e);
        }
    }

    // then, add a val for var_s
    expr val_for_var_s = exp.ctx().bv_val(v, 8);
    z3::func_decl decl_for_var_s = var_s.decl();
    random_model.add_const_interp(decl_for_var_s, val_for_var_s);

    return random_model;
}

bool sat_under_random_model(expr& exp, model& m, expr& var_s, int v) {
    model random_model(exp.ctx());
    unsigned num_constants = m.num_consts();

    //first, fix other variables
    for (unsigned i = 0; i <  num_constants; i++) {
        // TODO: decide the bit-vector size
        z3::func_decl decl = m.get_const_decl(i);
        z3::expr val_e = m.get_const_interp(decl);
        if (decl.name() != var_s.decl().name()) {
            random_model.add_const_interp(decl, val_e);
        }
    }

    // then, add a val for var_s
    expr val_for_var_s = exp.ctx().bv_val(v, 8);
    z3::func_decl decl_for_var_s = var_s.decl();
    random_model.add_const_interp(decl_for_var_s, val_for_var_s);

    // check if exp is satisfied by cur_model
    if (random_model.eval(exp, true).is_true()) { return true; }
    else { return false; }
}


// Expr is the pre condition
// Queries is the set of variables
void dump_optimize_objectives(expr& Expr, expr_vector& Queries, int mode) {
    z3::context& Ctx = Expr.ctx();
    z3::optimize Opt(Ctx);
    z3::params Param(Ctx);
    Param.set("priority", Ctx.str_symbol("box"));
    Opt.set(Param);
    Opt.add(Expr);

    for (unsigned i = 0; i < Queries.size(); i++) {
        if (mode == 1) {
            Opt.minimize(Queries[i]);
        } else if (mode == 2) {
            Opt.maximize(Queries[i]);
        } else {
            Opt.minimize(Queries[i]);
            Opt.maximize(Queries[i]);
        }
    }

    // output the constraints to a temp file in the dst
    std::string DstFileName = "";
    DstFileName.append("case");
    DstFileName.append(std::to_string(clock()));
    DstFileName.append(".opt.smt2");

    std::ofstream DstFile;
    DstFile.open(DstFileName);

    if (DstFile.is_open()) {
        DstFile << Opt << "\n";
        DstFile.close();
    } else {
        std::cerr << "File cannot be opened: " << DstFileName << "\n";
    }
}


#endif /* Z3PLUS_H_ */
