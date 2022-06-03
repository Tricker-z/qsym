#include <set>
#include <byteswap.h>
#include <iostream>
#include "solver.h"
#include "z3plus.h"

namespace qsym {
    
    namespace {
        
        const uint64_t kUsToS = 1000000;
        const int kSessionIdLength = 32;
        const unsigned kSolverTimeout = 10000; // 10 seconds
        const bool useOptSolver = false;    // decide if to use opt for optimistic solving
        const bool useAbsFuzz = true;
        const bool useAbsFuzzForTestsGeneration = true;
        
        std::string toString6digit(INT32 val) {
            char buf[6 + 1]; // ndigit + 1
            snprintf(buf, 7, "%06d", val);
            buf[6] = '\0';
            return std::string(buf);
        }
        
        uint64_t getTimeStamp() {
            struct timeval tv;
            gettimeofday(&tv, NULL);
            return tv.tv_sec * kUsToS + tv.tv_usec;
        }
        
        void parseConstSym(ExprRef e, Kind &op, ExprRef& expr_sym, ExprRef& expr_const) {
            for (INT32 i = 0; i < 2; i++) {
                expr_sym = e->getChild(i);
                expr_const = e->getChild(1 - i);
                if (!isConstant(expr_sym)
                    && isConstant(expr_const)) {
                    op = i == 0 ? e->kind() : swapKind(e->kind());
                    return;
                }
            }
            UNREACHABLE();
        }
        
        void getCanonicalExpr(ExprRef e,
                              ExprRef* canonical,
                              llvm::APInt* adjustment=NULL) {
            ExprRef first = NULL;
            ExprRef second = NULL;
            // e == Const + Sym --> canonical == Sym
            switch (e->kind()) {
                // TODO: handle Sub
                case Add:
                    first = e->getFirstChild();
                    second = e->getSecondChild();
                    if (isConstant(first)) {
                        *canonical = second;
                        if (adjustment != NULL)
                            *adjustment =
                                    static_pointer_cast<ConstantExpr>(first)->value();
                        return;
                        case Sub:
                            // C_0 - Sym
                            first = e->getFirstChild();
                        second = e->getSecondChild();
                        // XXX: need to handle reference count
                        if (isConstant(first)) {
                            *canonical = g_expr_builder->createNeg(second);
                            if (adjustment != NULL)
                                *adjustment = static_pointer_cast<ConstantExpr>(first)->value();
                            return;
                        }
                    }
                default:
                    break;
            }
            if (adjustment != NULL)
                *adjustment = llvm::APInt(e->bits(), 0);
            *canonical = e;
        }
        
        inline bool isEqual(ExprRef e, bool taken) {
            return (e->kind() == Equal && taken) ||
                   (e->kind() == Distinct && !taken);
        }
        
    } // namespace
    
    Solver::Solver(
            const std::string input_file,
            const std::string out_dir,
            const std::string bitmap)
            : input_file_(input_file)
            , inputs_()
            , out_dir_(out_dir)
            , context_(g_z3_context)
            , solver_(z3::solver(context_, "QF_BV"))
            , num_generated_(0)
            , trace_(bitmap)
            , last_interested_(false)
            , syncing_(false)
            , start_time_(getTimeStamp())
            , solving_time_(0)
            , total_solving_num_(0)
            , compute_interval_time_(0)
            , last_pc_(0)
            , dep_forest_()
    {
        // Set timeout for solver
        z3::params p(context_);
        p.set(":timeout", kSolverTimeout);
        solver_.set(p);
        
        checkOutDir();
        readInput();
    }
    
    void Solver::push() {
        solver_.push();
    }
    
    void Solver::reset() {
        solver_.reset();
    }
    
    void Solver::pop() {
        solver_.pop();
    }
    
    void Solver::add(z3::expr expr) {
        if (!expr.is_const())
            solver_.add(expr.simplify());
    }
    
    z3::check_result Solver::check() {
        total_solving_num_++;
        // does this work?
        //if (total_solving_num_ % 10 == 0) {
        LOG_STAT("=========================\nCurrent SMT query num:" +  decstr(total_solving_num_) + "\n, sovling time:" + decstr(solving_time_) + "\n =========\n");
        LOG_STAT("=========================\nCurrent interval time:" +  decstr(compute_interval_time_) + "\n =========\n");
        
        //  std::cout << " ===================================================\n";
        //  std::cout << "Current SMT query num: " << total_solving_num_ << "\n";
        //  std::cout << " ===================================================\n";
        //}
        uint64_t before = getTimeStamp();
        z3::check_result res;
        LOG_STAT(
                "SMT: { \"solving_time\": " + decstr(solving_time_) + ", "
                + "\"total_time\": " + decstr(before - start_time_) + " }\n");
        //LOG_DEBUG("Constraints: " + solver_.to_smt2() + "\n");
        try {
            res = solver_.check();
        }
        catch(z3::exception e) {
            // https://github.com/Z3Prover/z3/issues/419
            // timeout can cause exception
            res = z3::unknown;
        }
        uint64_t cur = getTimeStamp();
        uint64_t elapsed = cur - before;
        solving_time_ += elapsed;
        LOG_STAT("SMT: { \"solving_time\": " + decstr(solving_time_) + " }\n");
        return res;
    }
    
    bool Solver::checkAndSave(const std::string& postfix) {
        if (check() == z3::sat) {
            saveValues(postfix);
            return true;
        }
        else {
            LOG_DEBUG("unsat\n");
            return false;
        }
    }
    
    void Solver::addJcc(ExprRef e, bool taken, ADDRINT pc) {
        // Save the last instruction pointer for debugging
        last_pc_ = pc;
        
        if (e->isConcrete())
            return;
        
        // if e == Bool(true), then ignore
        if (e->kind() == Bool) {
            assert(!(castAs<BoolExpr>(e)->value()  ^ taken));
            return;
        }
        
        assert(isRelational(e.get()));
        
        // check duplication before really solving something,
        // some can be handled by range based constraint solving
        bool is_interesting;
        if (pc == 0) {
            // If addJcc() is called by special case, then rely on last_interested_
            is_interesting = last_interested_;
        }
        else
            is_interesting = isInterestingJcc(e, taken, pc);
        
        if (is_interesting)
            negatePath(e, taken);
        addConstraint(e, taken, is_interesting);
    }
    
    void Solver::addAddr(ExprRef e, ADDRINT addr) {
        llvm::APInt v(e->bits(), addr);
        addAddr(e, v);
    }
    
    void Solver::addAddr(ExprRef e, llvm::APInt addr) {
        if (e->isConcrete())
            return;
        
        if (last_interested_) {
            uint64_t before = getTimeStamp();
            
            reset();
            // TODO: add optimize in z3
            syncConstraints(e);
            if (check() != z3::sat)
                return;
            z3::expr &z3_expr = e->toZ3Expr();
            
            // TODO: add unbound case
            if (useOptSolver) {
                // TODO:
                // getMinValue and getMaxValue will save all solutions
                // but get_abstract_interval_as_expr only finds min_expr and max_expr
                // we should decide if to use it or not
                
                // First, solve once
                
                checkAndSave();
                
                // Second, get the interval
                z3::expr_vector interval(context_);
                z3::expr cur_assertions = z3::mk_and(solver_.assertions());
                get_abstract_interval_as_expr(cur_assertions, z3_expr, interval, 6000);
                z3::expr min_expr = interval[0];
                z3::expr max_expr = interval[1];
                
                // Third, solve twice
                if (!(min_expr.is_false())) {
                    solveOne(z3_expr == min_expr);
                }
                if (!(max_expr.is_false())) {
                    solveOne(z3_expr == max_expr);
                }
                
                // Finally, mutate the model?
                // TODO: what values should be fixed?
                // How many variables does z3_expr have
                z3::expr_vector z3_expr_vars(context_);
                get_expr_vars(z3_expr, z3_expr_vars);
                // use mutate to get model!!!!
                
                
                
                
            } else {
                z3::expr min_expr = getMinValue(z3_expr);
                z3::expr max_expr = getMaxValue(z3_expr);
                solveOne(z3_expr == min_expr);
                solveOne(z3_expr == max_expr);
            }
            
            uint64_t cur = getTimeStamp();
            uint64_t elapsed = cur - before;
            compute_interval_time_ += elapsed;
            LOG_STAT("SMT: { \"compute_interal_time\": " + decstr(compute_interval_time_) + " }\n");
        }
        addValue(e, addr);  // why
    }
    
    void Solver::addValue(ExprRef e, ADDRINT val) {
        llvm::APInt v(e->bits(), val);
        addValue(e, v);
    }
    
    void Solver::addValue(ExprRef e, llvm::APInt val) {
        if (e->isConcrete())
            return;

#ifdef CONFIG_TRACE
        trace_addValue(e, val);
#endif
        
        ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());
        ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);
        
        addConstraint(expr_concrete, true, false);
    }
    
    void Solver::solveAll(ExprRef e, llvm::APInt val) {
        if (last_interested_) {
            std::string postfix = "";
            ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());
            ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);
            
            reset();
            syncConstraints(e);
            addToSolver(expr_concrete, false);
            
            if (check() != z3::sat) {
                // Optimistic solving
                reset();
                addToSolver(expr_concrete, false);
                postfix = "optimistic";
            }
            
            z3::expr z3_expr = e->toZ3Expr();
            while(true) {
                if (!checkAndSave(postfix))
                    break;
                z3::expr value = getPossibleValue(z3_expr);
                add(value != z3_expr);
            }
        }
        addValue(e, val);
    }
    
    UINT8 Solver::getInput(ADDRINT index) {
        assert(index < inputs_.size());
        return inputs_[index];
    }
    
    void Solver::checkOutDir() {
        // skip if there is no out_dir
        if (out_dir_.empty()) {
            LOG_INFO("Since output directory is not set, use stdout\n");
            return;
        }
        
        struct stat info;
        if (stat(out_dir_.c_str(), &info) != 0
            || !(info.st_mode & S_IFDIR)) {
            LOG_FATAL("No such directory\n");
            exit(-1);
        }
    }
    
    void Solver::readInput() {
        std::ifstream ifs (input_file_, std::ifstream::in | std::ifstream::binary);
        if (ifs.fail()) {
            LOG_FATAL("Cannot open an input file\n");
            exit(-1);
        }
        
        char ch;
        while (ifs.get(ch))
            inputs_.push_back((UINT8)ch);
    }
    
    std::vector<std::vector<UNIT8>> Solver::getConcreteValues() {
        std::vector<std::vector<UNIT8>> values_set;

        // TODO: change from real input
        z3::model m = solver_.get_model();
        unsigned num_constants = m.num_consts();
        std::vector<UINT8> values = inputs_;
        int modify_cnt = 0;
        
        // get the cared variables and their indexes
        std::vector<z3::expr> var_index_pairs;
        
        LOG_STAT("Input Offset : \n");
        for (unsigned i = 0; i < num_constants; i++) {
            z3::func_decl decl = m.get_const_decl(i);
            z3::expr e = m.get_const_interp(decl);
            z3::symbol name = decl.name();
            
            
            if (name.kind() == Z3_INT_SYMBOL) {
                LOG_STAT(" " + decstr(i));
                int value = e.get_numeral_int();
                modify_cnt++;
                values[name.to_int()] = (UINT8)value;
                z3::expr var_e = decl();
                var_index_pairs.push_back(var_e);
            }
        }
        LOG_STAT("\nOUTPUT:   INPUT SIZE------: " + decstr(values.size()) + "   Modify size:     " + decstr(modify_cnt) + "        \n===============================\n");

        // The values returned by qsym
        values_set.push_back(values);

        if (useAbsFuzz) {
            z3::expr cur_assertions = z3::mk_and(solver_.assertions());

            if (var_index_pairs.size() == 1) {
                /*
                 * Single variable:
                 */

                LOG_STAT("AbsFuzz: only single variable\n");
                // First, get interval information
                LOG_STAT("Interval Information:\n");
                z3::expr& var_s = var_index_pairs[0];
                z3::expr_vector interval_s(context_);
                z3::expr_vector interval_s(context_);
                get_abstract_interval_as_expr(cur_assertions, var_s, interval_s, 5000);
                z3::expr min_expr_s = interval_s[0];
                z3::expr max_expr_s = interval_s[1];
                std::vector<int> interval_s_num;  // the numerical interval
                if (!min_expr_s.is_false()) {
                    interval_s_num.push_back((UINT8)(min_expr_s.get_numeral_int()));
                    LOG_STAT("MIN: " + decstr(min_expr_s.get_numeral_int()));
                } else {
                    interval_s_num.push_back((UINT8)(0));
                    LOG_STAT("MIN: " + decstr(0));
                }
                if (!max_expr_s.is_false()) {
                    interval_s_num.push_back((UINT8)(max_expr_s.get_numeral_int()));
                    LOG_STAT("MAX: " + decstr(max_expr_s.get_numeral_int()) + "\n ");
                } else {
                    interval_s_num.push_back((UINT8)(40096));
                    LOG_STAT("MAX: " + decstr(0) + "\n ");
                }

                // The interval is not unbounded, we test 10 random model
                if (interval_s_num[0] > 0 || interval_s_num[1] < 255) {
                    if (interval_s_num[0] != interval_s_num[1]) {
                        LOG_STAT("AbsFuzz: interval bounded, and not fixed!!!!\n");
                        int x_random_models_tested = 0;
                        for (int k = interval_s_num[0]; k <= interval_s_num[1]; k++) {
                            if (sat_under_random_model(cur_assertions, m, var_s, k)) {
                                LOG_STAT("AbsFuzz: random model success!!!!\n");
                                // Now generate new inputs
                                if (useAbsFuzzForTestsGeneration) {
                                    z3::model& randmodel = get_random_model(cur_assertions, m, var_s, k);
                                    std::vector<UINT8> values_from_randmodel = inputs_;
                                    for (unsigned i = 0; i < num_constants; i++) {
                                        z3::func_decl decl = randmodel.get_const_decl(i);
                                        z3::expr e = randmodel.get_const_interp(decl);
                                        z3::symbol name = decl.name();
                                        if (name.kind() == Z3_INT_SYMBOL) {
                                            int value = e.get_numeral_int();
                                            values_from_randmodel[name.to_int()] = (UINT8)value;
                                        }
                                    }
                                    // store the new values
                                    values_set.push_back(values_from_randmodel);
                                }
                            } else {
                                LOG_STAT("AbsFuzz: random model fail!!!!\n");
                            }
                            x_random_models_tested++;
                            if (x_random_models_tested == 10) {
                                break;
                            }
                        }
                    }
                }

            } else if (var_index_pairs.size() > 1) {
                /*
                 *
                 * Multiple Variables
                 */

                // First, test partial model
                z3::expr_vector real_donot_cared_vars(context_);
                for (auto& var_i : var_index_pairs) {
                    z3::expr_vector potential_donot_cared_vars(context_);
                    potential_donot_cared_vars.push_back(var_i);
                    // every time, we only consider one variable as "don't cares"
                    bool var_i_irrelevant = sat_under_partial_model(cur_assertions, m, potential_donot_cared_vars);
                    if (var_i_irrelevant) {
                        // print var_i.decl().name().to_int();
                        LOG_STAT("AbsFuzz: partial model success!!!!\n");
                        real_donot_cared_vars.push_back(var_i);
                    }
                }

                // Each var_s is a don't care variable
                // Now generate new inputs
                if (useAbsFuzzForTestsGeneration) {
                    for (z3::expr& var_s : real_donot_cared_vars) {
                        // TODO: how many models to generate
                        int num_models_to_generate = 5;
                        // TODO: where to start from?
                        for (int i = 0; i <= num_models_to_generate; i++) {
                            z3::model& randmodel = get_random_model(cur_assertions, m, var_s, i);
                            std::vector<UINT8> values_from_randmodel = inputs_;
                            for (unsigned i = 0; i < num_constants; i++) {
                                z3::func_decl decl = randmodel.get_const_decl(i);
                                z3::expr e = randmodel.get_const_interp(decl);
                                z3::symbol name = decl.name();
                                if (name.kind() == Z3_INT_SYMBOL) {
                                    int value = e.get_numeral_int();
                                    values_from_randmodel[name.to_int()] = (UINT8)value;
                                }
                            }
                            // store the new values
                            values_set.push_back(values_from_randmodel);
                        }
                    }
                }

                // Then, Check Interval Information
                LOG_STAT("AbsFuzz: multiple variables\n");
                LOG_STAT("Interval Information:\n");
                for (auto& var_i : var_index_pairs) {
                    z3::expr_vector interval_i(context_);
                    get_abstract_interval_as_expr(cur_assertions, var_i, interval_i, 5000);
                    z3::expr min_expr_i = interval_i[0];
                    z3::expr max_expr_i = interval_i[1];
                    std::vector<int> interval_i_num;  // the numerical interval
                    if (!min_expr_i.is_false()) {
                        interval_i_num.push_back((UINT8)(min_expr_i.get_numeral_int()));
                        LOG_STAT("MIN: " + decstr(min_expr_i.get_numeral_int()));
                    } else {
                        interval_i_num.push_back((UINT8)(0));
                        LOG_STAT("MIN: " + decstr(0));
                    }
                    if (!max_expr_i.is_false()) {
                        interval_i_num.push_back((UINT8)(max_expr_i.get_numeral_int()));
                        LOG_STAT("MAX: " + decstr(max_expr_i.get_numeral_int()) + "\n ");
                    } else {
                        interval_i_num.push_back((UINT8)(40096));
                        LOG_STAT("MAX: " + decstr(0) + "\n ");
                    }
                    // TODO: mutate
                }
            }
        }
        return values_set;
    }
    
    void Solver::saveValues(const std::string& postfix) {
        // std::vector<UINT8> values = getConcreteValues();
        std::vector<std::vector<UNIT8>> values_set = getConcreteValues();
        
        for (std::vector<UINT8> values : values_set) {
            // If no output directory is specified, then just print it out
            if (out_dir_.empty()) {
                printValues(values);
                return;
            }

            std::string fname = out_dir_+ "/" + toString6digit(num_generated_);
            // Add postfix to record where it is genereated
            if (!postfix.empty())
                fname = fname + "-" + postfix;
            ofstream of(fname, std::ofstream::out | std::ofstream::binary);
            LOG_INFO("New testcase: " + fname + "\n");
            if (of.fail())
                LOG_FATAL("Unable to open a file to write results\n");

            // TODO: batch write
            for (unsigned i = 0; i < values.size(); i++) {
                char val = values[i];
                of.write(&val, sizeof(val));
            }

            of.close();
            num_generated_++;
        }
    }
    
    void Solver::printValues(const std::vector<UINT8>& values) {
        fprintf(stderr, "[INFO] Values: ");
        for (unsigned i = 0; i < values.size(); i++) {
            fprintf(stderr, "\\x%02X", values[i]);
        }
        fprintf(stderr, "\n");
    }
    
    z3::expr Solver::getPossibleValue(z3::expr& z3_expr) {
        z3::model m = solver_.get_model();
        return m.eval(z3_expr);
    }
    
    z3::expr Solver::getMinValue(z3::expr& z3_expr) {
        push();
        z3::expr value(context_);
        while (true) {
            if (checkAndSave()) {
                value = getPossibleValue(z3_expr);
                solver_.add(z3::ult(z3_expr, value));
            }
            else
                break;
        }
        pop();
        return value;
    }
    
    z3::expr Solver::getMaxValue(z3::expr& z3_expr) {
        push();
        z3::expr value(context_);
        while (true) {
            if (checkAndSave()) {
                value = getPossibleValue(z3_expr);
                solver_.add(z3::ugt(z3_expr, value));
            }
            else
                break;
        }
        pop();
        return value;
    }
    
    void Solver::addToSolver(ExprRef e, bool taken) {
        e->simplify();
        if (!taken)
            e = g_expr_builder->createLNot(e);
        add(e->toZ3Expr());
    }
    
    void Solver::syncConstraints(ExprRef e) {
        std::set<std::shared_ptr<DependencyTree<Expr>>> forest;
        DependencySet* deps = e->getDependencies();
        
        for (const size_t& index : *deps)
            forest.insert(dep_forest_.find(index));
        
        for (std::shared_ptr<DependencyTree<Expr>> tree : forest) {
            std::vector<std::shared_ptr<Expr>> nodes = tree->getNodes();
            for (std::shared_ptr<Expr> node : nodes) {
                if (isRelational(node.get()))
                    addToSolver(node, true);
                else {
                    // Process range-based constraints
                    bool valid = false;
                    for (INT32 i = 0; i < 2; i++) {
                        ExprRef expr_range = getRangeConstraint(node, i);
                        if (expr_range != NULL) {
                            addToSolver(expr_range, true);
                            valid = true;
                        }
                    }
                    
                    // One of range expressions should be non-NULL
                    if (!valid)
                        LOG_INFO(std::string(__func__) + ": Incorrect constraints are inserted\n");
                }
            }
        }
        
        checkFeasible();
    }
    
    void Solver::addConstraint(ExprRef e, bool taken, bool is_interesting) {
        if (auto NE = castAs<LNotExpr>(e)) {
            addConstraint(NE->expr(), !taken, is_interesting);
            return;
        }
        if (!addRangeConstraint(e, taken))
            addNormalConstraint(e, taken);
    }
    
    void Solver::addConstraint(ExprRef e) {
        // If e is true, then just skip
        if (e->kind() == Bool) {
            QSYM_ASSERT(castAs<BoolExpr>(e)->value());
            return;
        }
        dep_forest_.addNode(e);
    }
    
    bool Solver::addRangeConstraint(ExprRef e, bool taken) {
        if (!isConstSym(e))
            return false;
        
        Kind kind = Invalid;
        ExprRef expr_sym, expr_const;
        parseConstSym(e, kind, expr_sym, expr_const);
        ExprRef canonical = NULL;
        llvm::APInt adjustment;
        getCanonicalExpr(expr_sym, &canonical, &adjustment);
        llvm::APInt value = static_pointer_cast<ConstantExpr>(expr_const)->value();
        
        if (!taken)
            kind = negateKind(kind);
        
        canonical->addConstraint(kind, value,
                                 adjustment);
        addConstraint(canonical);
        //updated_exprs_.insert(canonical);
        return true;
    }
    
    void Solver::addNormalConstraint(ExprRef e, bool taken) {
        if (!taken)
            e = g_expr_builder->createLNot(e);
        addConstraint(e);
    }
    
    ExprRef Solver::getRangeConstraint(ExprRef e, bool is_unsigned) {
        Kind lower_kind = is_unsigned ? Uge : Sge;
        Kind upper_kind = is_unsigned ? Ule : Sle;
        RangeSet *rs = e->getRangeSet(is_unsigned);
        if (rs == NULL)
            return NULL;
        
        ExprRef expr = NULL;
        for (auto i = rs->begin(), end = rs->end();
             i != end; i++) {
            const llvm::APSInt& from = i->From();
            const llvm::APSInt& to = i->To();
            ExprRef bound = NULL;
            
            if (from == to) {
                // can simplify this case
                ExprRef imm = g_expr_builder->createConstant(from, e->bits());
                bound = g_expr_builder->createEqual(e, imm);
            }
            else
            {
                ExprRef lb_imm = g_expr_builder->createConstant(i->From(), e->bits());
                ExprRef ub_imm = g_expr_builder->createConstant(i->To(), e->bits());
                ExprRef lb = g_expr_builder->createBinaryExpr(lower_kind, e, lb_imm);
                ExprRef ub = g_expr_builder->createBinaryExpr(upper_kind, e, ub_imm);
                bound = g_expr_builder->createLAnd(lb, ub);
            }
            
            if (expr == NULL)
                expr = bound;
            else
                expr = g_expr_builder->createLOr(expr, bound);
        }
        
        return expr;
    }
    
    
    bool Solver::isInterestingJcc(ExprRef rel_expr, bool taken, ADDRINT pc) {
        bool interesting = trace_.isInterestingBranch(pc, taken);
        // record for other decision
        last_interested_ = interesting;
        return interesting;
    }
    
    void Solver::negatePath(ExprRef e, bool taken) {
        reset();
        syncConstraints(e);
        addToSolver(e, !taken);
        bool sat = checkAndSave();
        if (!sat) {
            reset();
            // optimistic solving
            addToSolver(e, !taken);
            checkAndSave("optimistic");
        }
    }
    
    void Solver::solveOne(z3::expr z3_expr) {
        push();
        add(z3_expr);
        checkAndSave();
        pop();
    }
    
    void Solver::checkFeasible() {
#ifdef CONFIG_TRACE
        if (check() == z3::unsat)
    LOG_FATAL("Infeasible constraints: " + solver_.to_smt2() + "\n");
#endif
    }
    
} // namespace qsym
