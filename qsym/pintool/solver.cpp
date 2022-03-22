#include <set>
#include <byteswap.h>
#include "solver.h"

#include "call_stack_manager.h"

#define HYBRID_DBG_CHECK_PI_SAT 0

extern "C" {
  int _sym_is_emulation_mode_enabled();
}

namespace qsym {

namespace {

const uint64_t kUsToS = 1000000;
const int kSessionIdLength = 32;
const unsigned kSolverTimeout = 10000; // 10 seconds

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
  , context_(*g_z3_context)
  , solver_(z3::solver(context_, "QF_BV"))
  , num_generated_(0)
  , trace_(bitmap)
  , last_interested_(false)
  , syncing_(false)
  , start_time_(getTimeStamp())
  , solving_time_(0)
  , last_pc_(0)
  , dep_forest_()
{
  // Set timeout for solver
  z3::params p(context_);
  p.set(":timeout", kSolverTimeout);
  solver_.set(p);

  checkOutDir();
  readInput();
#if SYMFUSION_USE_AVOID_CACHE
  if (getenv("SYMFUSION_AVOID_CACHE_DIR")) {
    usePersistentAvoidCache = true;
    persistent_cache = std::string(getenv("SYMFUSION_AVOID_CACHE_DIR"));
  }
#endif
}

void Solver::push() {
  solver_.push();
}

void Solver::reset() {
#if SYMFUSION_USE_AVOID_CACHE
  query_hash = 0;
#endif
  solver_.reset();
}

void Solver::pop() {
  solver_.pop();
}

void Solver::add(z3::expr expr) {
  if (!expr.is_const())
    solver_.add(expr); // expr.simplify()
}

z3::check_result Solver::check() {
  uint64_t before = getTimeStamp();
  z3::check_result res;
  LOG_STAT(
      "SMT: { \"solving_time\": " + decstr(solving_time_) + ", "
      + "\"total_time\": " + decstr(before - start_time_) + " }\n");
  // LOG_DEBUG("Constraints: " + solver_.to_smt2() + "\n");
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

#if SYMFUSION_USE_AVOID_CACHE
  if (usePersistentAvoidCache) {
    std::string f = persistent_cache + "/" + std::to_string(query_hash);
    std::ifstream ifs(f, std::ifstream::in | std::ifstream::binary);
    if (!ifs.fail()) {
      ifs.close();
      printf("Avoiding query with hash %lx\n", query_hash);
      return false;
    }
    ifs.close();
    std::ofstream of(f, std::ofstream::out | std::ofstream::binary);
    if (of.fail()) {
      printf("Unable to open a file to write results\n");
      abort();
    }
    of.close();
  }
#endif

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

  if (!isRelational(e.get())) {

    // fix: when a bool is written/read from memory,
    //      the runtime converts it to bits however
    //      symcc keeps to treat it as a bool

    if (auto ex_e = castAs<ExtractExpr>(e)) 
      if (ex_e->index() == 0 && (ex_e->bits() == 8 || ex_e->bits() == 1)) {
        if (isRelational(ex_e->getChild(0).get())) {
          e = ex_e->getChild(0);
        } else if (auto ite_e = castAs<IteExpr>(ex_e->getChild(0))) {
          e = ex_e->getChild(0);
        } else if (ex_e->bits() == 1) {
          e = g_expr_builder->createEqual(e, g_expr_builder->createConstant(1, ex_e->bits()));
        }
      }

    if (auto ite_e = castAs<IteExpr>(e)) {
      if (ite_e->getChild(1)->isOne() && ite_e->getChild(2)->isZero()) {
        e = ite_e->getChild(0);
      } else if (ite_e->getChild(1)->isZero() && ite_e->getChild(2)->isOne()) {
        e = g_expr_builder->createLNot(ite_e->getChild(0));
      }
    }
  }

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

  // is_interesting = false;
#if 0
  if (is_interesting) {
    printf("INTERESTING QUERY at %lx taken=%d\n", pc, taken);
    // printf("INTERESTING QUERY: %s\n", e->toString().c_str());
  }
#endif
  if (is_interesting)
    negatePath(e, taken);
  addConstraint(e, taken, is_interesting);

#if HYBRID_DBG_CHECK_PI_SAT
  reset();
  LOG_INFO("Checking PI\n");
  syncConstraints(e);
  if(solver_.check() == z3::unsat) {
    LOG_FATAL("Adding infeasible constraints: " + std::string(taken ? "" : "!") + e->toString() + "\n");
    abort();
  } else {
    // printf("\nPI OK\n\n");
  }
  reset();
#endif
}

void Solver::addAddr(ExprRef e, ADDRINT addr) {
  llvm::APInt v(e->bits(), addr);
  addAddr(e, v);
}

void Solver::addAddr(ExprRef e, llvm::APInt addr) {
  if (e->isConcrete())
    return;

  if (last_interested_) {
    reset();
    // TODO: add optimize in z3
    syncConstraints(e);
    if (check() != z3::sat)
      return;
    z3::expr &z3_expr = e->toZ3Expr();

    // TODO: add unbound case
    z3::expr min_expr = getMinValue(z3_expr);
    z3::expr max_expr = getMaxValue(z3_expr);
    solveOne(z3_expr == min_expr);
    solveOne(z3_expr == max_expr);
  }

  addValue(e, addr);
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

std::vector<UINT8> Solver::getConcreteValues() {
  // TODO: change from real input
  z3::model m = solver_.get_model();
  unsigned num_constants = m.num_consts();
  std::vector<UINT8> values = inputs_;
  for (unsigned i = 0; i < num_constants; i++) {
    z3::func_decl decl = m.get_const_decl(i);
    z3::expr e = m.get_const_interp(decl);
    z3::symbol name = decl.name();

    if (name.kind() == Z3_INT_SYMBOL) {
      int value = e.get_numeral_int();
      values[name.to_int()] = (UINT8)value;
    }
  }
  return values;
}

void Solver::saveValues(const std::string& postfix) {
  std::vector<UINT8> values = getConcreteValues();

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

  // printf("CONSTRAINT: %s\n", e->toString().c_str());

  z3::expr z3_e = e->toZ3Expr();
#if SYMFUSION_USE_AVOID_CACHE
  query_hash ^= z3_e.hash(); 
#endif
  add(z3_e);
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
  // if (!addRangeConstraint(e, taken))
    addNormalConstraint(e, taken);
}

void Solver::addConstraint(ExprRef e) {
  // printf("CONSTRAINT: %s\n", e->toString().c_str());
  // If e is true, then just skip
  if (e->kind() == Bool) {
    QSYM_ASSERT(castAs<BoolExpr>(e)->value());
    return;
  }
  if (e->isConcrete())
    return;
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
  // printf("interesting %d at %lx\n", interesting, pc);
  // record for other decision
  last_interested_ = interesting;
  return interesting;
}

void Solver::negatePath(ExprRef e, bool taken) {
  reset();
  syncConstraints(e);

#if HYBRID_DBG_CHECK_PI_SAT
  if(solver_.check() == z3::unsat) {
    LOG_FATAL("Infeasible constraints: " + solver_.to_smt2() + "\n");
    abort();
  } else {
    // printf("PI OK\n");
  }
#endif

  addToSolver(e, !taken);
  bool sat = checkAndSave();
#if 0
  if (sat && !_sym_is_emulation_mode_enabled() && e->isLibGenerated()) {
    printf("Branch query involves library generated expressions\n");
    g_call_stack_manager.printStack();
    printf("\n\n\n");
  }
#endif

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

static Z3_model m = NULL;
int Solver::checkConsistency(ExprRef e, uint64_t expected_value) {

  if (m == NULL) {
    Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
    std::vector<UINT8> values = inputs_;
    m = Z3_mk_model(context_);
    Z3_model_inc_ref(context_, m);
    Z3_sort sort = Z3_mk_bv_sort(context_, 8);
    for (size_t i = 0; i < inputs_.size(); i++) {

      z3::symbol s = context_.int_symbol(i);
      z3::expr v = context_.bv_val(inputs_[i], 8);
      
      // printf("%s\n", Z3_ast_to_string(context_, v));

      Z3_func_decl decl = Z3_mk_func_decl(context_, s, 0, NULL, sort);
      Z3_add_const_interp(context_, m, decl, v);
    }

    // printf("Model:\n%s\n", Z3_model_to_string(context_, m));
  }

  // printf("EXPR: %s\n", Z3_ast_to_string(context_, e->toZ3Expr()));

  uint64_t  value;
  Z3_ast    solution;
  Z3_bool   successfulEval =
      Z3_model_eval(context_, m, e->toZ3Expr(), Z3_TRUE, &solution);
  assert(successfulEval && "Failed to evaluate model");

  if (Z3_get_ast_kind(context_, solution) == Z3_NUMERAL_AST) {
    Z3_bool successGet =
          Z3_get_numeral_uint64(context_, solution, (uint64_t*)&value);
    assert(successGet);
    if (value != expected_value) {
      Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
      printf("[%d] %s\n", successGet, Z3_ast_to_string(context_, e->toZ3Expr()));
      printf("FAILURE: %lx vs %lx\n", value, expected_value);
    } else {
      printf("SUCCESS: %lx vs %lx\n", value, expected_value);
    }
    return value == expected_value;
  } else {

    Z3_lbool res = Z3_get_bool_value(context_, solution);
    if (res == Z3_L_TRUE) {
      value = 1;
      if (value != expected_value) {
        Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
        printf("%s\n", Z3_ast_to_string(context_, e->toZ3Expr()));
        printf("BOOL FAILURE: %lx vs %lx\n", value, expected_value);
      }
      return value == expected_value;
    } else if (res == Z3_L_FALSE) {
      value = 0;
      if (value != expected_value) {
        Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
        printf("%s\n", Z3_ast_to_string(context_, e->toZ3Expr()));
        printf("BOOL FAILURE: %lx vs %lx\n", value, expected_value);
      }
      return value == expected_value;
    } else {
      printf("KIND: %x\n", Z3_get_ast_kind(context_, solution));
      Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
      printf("EXPR: %s\n", Z3_ast_to_string(context_, e->toZ3Expr()));
      assert(0 && "Cannot evaluate");
      abort();
    }
  }
}

} // namespace qsym
