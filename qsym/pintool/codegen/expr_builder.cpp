#include "expr_builder.h"
#include "solver.h"
#include "call_stack_manager.h"
#include <llvm/ADT/StringRef.h>

extern "C" {
  int _sym_is_emulation_mode_enabled();
}

namespace qsym {

namespace {
const INT32 kComplexityThresholdForSimplify = 16;

void addUses(ExprRef e) {
  for (INT i = 0; i < e->num_children(); i++)
    e->getChild(i)->addUse(e);
}

// utility function for checking values
bool isZero(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isZero();
}

bool isOne(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isOne();
}

bool isAllOnes(ExprRef e) {
  ConstantExprRef ce = castAs<ConstantExpr>(e);
  return ce != NULL && ce->isAllOnes();
}

} // namespace

bool canEvaluateTruncated(ExprRef e, UINT bits, UINT depth=0) {
  if (depth > 1)
    return false;

  switch (e->kind()) {
    default:
      return false;
    case Mul:
      return canEvaluateTruncated(e->getChild(0), depth + 1)
        && canEvaluateTruncated(e->getChild(1), depth + 1);
    case UDiv:
    case URem: {
      UINT high_bits = e->bits() - bits;
      if (e->getChild(0)->countLeadingZeros() >= high_bits
          && e->getChild(1)->countLeadingZeros() >= high_bits) {
        return canEvaluateTruncated(e->getChild(0), depth + 1)
          && canEvaluateTruncated(e->getChild(1), depth + 1);
      }
      else
        return false;
    }
    case ZExt:
    case SExt:
    case Constant:
    case Concat:
      return true;
  }
}

ExprRef evaluateInDifferentType(ExprBuilder* builder, ExprRef op, UINT32 index, UINT32 bits) {
  // TODO: recursive evaluation
  switch (op->kind()) {
    default:
      return NULL;
    case Mul:
    case UDiv:
    case URem: {
      ExprRef e1 = builder->createExtract(op->getChild(0), index, bits);
      ExprRef e2 = builder->createExtract(op->getChild(1), index, bits);

      return builder->createBinaryExpr(op->kind(),
          builder->createExtract(op->getChild(0), index, bits),
          builder->createExtract(op->getChild(1), index, bits));
    }
  }
}

ExprBuilder::ExprBuilder() : next_(NULL) {}

void ExprBuilder::setNext(ExprBuilder* next) {
  next_ = next;
}

ExprBuilder* SymbolicExprBuilder::create() {
  ExprBuilder* base = new BaseExprBuilder();
  ExprBuilder* commu = new CommutativeExprBuilder();
  ExprBuilder* common = new CommonSimplifyExprBuilder();
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* symbolic = new SymbolicExprBuilder();
  ExprBuilder* cache = new CacheExprBuilder();

  // commu -> symbolic -> common -> constant folding -> base
  commu->setNext(symbolic);
  symbolic->setNext(common);
  common->setNext(const_folding);
  const_folding->setNext(cache);
  cache->setNext(base);
  return commu;
}

ExprBuilder* ConstantFoldingExprBuilder::create() {
  // constant folding -> base
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* base = new BaseExprBuilder();

  // commu -> symbolic -> common -> constant folding -> base
  const_folding->setNext(base);
  return const_folding;
}

ExprRef ExprBuilder::createTrue() {
  return createBool(true);
}

ExprRef ExprBuilder::createFalse() {
  return createBool(false);
}

ExprRef ExprBuilder::createMsb(ExprRef e) {
  return createExtract(e, e->bits() - 1, 1);
}

ExprRef ExprBuilder::createLsb(ExprRef e) {
  return createExtract(e, 0, 1);
}

ExprRef ExprBuilder::bitToBool(ExprRef e) {
  QSYM_ASSERT(e->bits() == 1);
  ExprRef one = createConstant(1, e->bits());
  return createEqual(e, one);
}

ExprRef ExprBuilder::boolToBit(ExprRef e, UINT32 bits) {
  ExprRef e1 = createConstant(1, bits);
  ExprRef e0 = createConstant(0, bits);

  if (!isRelational(e.get())) {
    if (auto ex_e = castAs<ExtractExpr>(e))
      if (ex_e->index() == 0 && ex_e->bits() == 8) {
        // a bool variable may be written and then read back
        // this will generate an extract over a boolean,
        // which is invalid. 

        return createIte(e->getChild(0), e1, e0);
      }

    // linearization may have concretized the value
    if (auto ce = castAs<ConstantExpr>(e)) {
      ADDRINT res = ce->value().getLimitedValue();
      if (res) return e1;
      else return e0;
    }
  }

  return createIte(e, e1, e0);
}

ExprRef ExprBuilder::createConcat(std::list<ExprRef> exprs) {
  assert(!exprs.empty());
  auto it = exprs.begin();

  // get a first element from the list
  ExprRef e = *it;
  it++;

  for (; it != exprs.end(); it++)
    e = createConcat(e, *it);

  return e;
}

ExprRef ExprBuilder::createLAnd(std::list<ExprRef> exprs) {
  assert(!exprs.empty());
  auto it = exprs.begin();

  // get a first element from the list
  ExprRef e = *it;
  it++;

  for (; it != exprs.end(); it++)
    e = createLAnd(e, *it);

  return e;
}

ExprRef ExprBuilder::createTrunc(ExprRef e, UINT32 bits) {
  return createExtract(e, 0, bits);
}

ExprRef BaseExprBuilder::createRead(ADDRINT off) {
  static std::vector<ExprRef> cache;
  if (off >= cache.size())
    cache.resize(off + 1);

  if (cache[off] == NULL)
    cache[off] = std::make_shared<ReadExpr>(off);

  return cache[off];
}

ExprRef BaseExprBuilder::createExtract(ExprRef e, UINT32 index, UINT32 bits)
{
  if (bits == e->bits())
    return e;

#if 0
  if (isRelational(e.get())) {
    printf("Invalid Extract: %s\n", e->toString().c_str());
    abort();
  }
#endif
  
  if (isRelational(e.get()))
    e = boolToBit(e, bits);

  ExprRef ref = std::make_shared<ExtractExpr>(e, index, bits);
  addUses(ref);
  return ref;
}

ExprRef
CacheExprBuilder::findOrInsert(ExprRef new_expr) {
  if (ExprRef cached = findInCache(new_expr))
    return cached;
  QSYM_ASSERT(new_expr != NULL);
  insertToCache(new_expr);
  return new_expr;
}

void CacheExprBuilder::insertToCache(ExprRef e) {
  cache_.insert(e);
}

ExprRef CacheExprBuilder::findInCache(ExprRef e) {
  return cache_.find(e);
}

ExprRef CommutativeExprBuilder::createSub(ExprRef l, ExprRef r)
{
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (nce_l != NULL && ce_r != NULL) {
    // X - C_0 = -C_0 + X
    return createAdd(createNeg(ce_r), nce_l);
  }
  else
    return ExprBuilder::createSub(l, r);
}

ExprRef CommonSimplifyExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(E(e, x, y), E(e, y, z)) => E(e, x, z)
  if (auto ee_l = castAs<ExtractExpr>(l)) {
    if (auto ee_r = castAs<ExtractExpr>(r)) {
      if (ee_l->expr() == ee_r->expr()
          && ee_r->index() + ee_r->bits() == ee_l->index()) {
        return createExtract(ee_l->expr(), ee_r->index(), ee_r->bits() + ee_l->bits());
      }
    }
  }

  // C(E(Ext(e), e->bits(), bits), e) == E(Ext(e), 0, e->bits() + bits)
  if (auto ee_l = castAs<ExtractExpr>(l)) {
    if (auto ext = castAs<ExtExpr>(ee_l->expr())) {
      if (ee_l->index() == r->bits()
          && equalShallowly(*ext->expr(), *r)) {
        // Here we used equalShallowly
        // because same ExtractExpr can have different addresses,
        // but using deep comparison is expensive
        return createExtract(ee_l->expr(), 0, ee_l->bits() + r->bits());
      }
    }
  }

  if (auto ite = castAs<IteExpr>(l)) {
    if (auto const_r = castAs<ConstantExpr>(r)) {
      if (auto ite_child1 = castAs<ConstantExpr>(l->getChild(1))) {
        if (auto ite_child2 = castAs<ConstantExpr>(l->getChild(2))) {
          return createIte(ite->getChild(0), createConcat(ite->getChild(1), const_r), createConcat(ite->getChild(2), const_r));
        }
      }
    }
  }

  if (auto ite = castAs<IteExpr>(r)) {
    if (auto const_l = castAs<ConstantExpr>(l)) {
      if (auto ite_child1 = castAs<ConstantExpr>(ite->getChild(1))) {
        if (auto ite_child2 = castAs<ConstantExpr>(ite->getChild(2))) {
          return createIte(ite->getChild(0), createConcat(const_l, ite->getChild(1)), createConcat(const_l, ite->getChild(2)));
        }
      }
    }
  }

  if (auto ce_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      if (auto ce_child1 = castAs<ConstantExpr>(r->getChild(0))) {
        return createConcat(createConcat(ce_l, ce_child1), r->getChild(1));
      }
    }
  }

  return ExprBuilder::createConcat(l, r);
}

ExprRef CommonSimplifyExprBuilder::createLNot(ExprRef e) {
  return ExprBuilder::createLNot(e);
}

ExprRef CommonSimplifyExprBuilder::createExtract(
    ExprRef e, UINT32 index, UINT32 bits) {
  if (auto ce = castAs<ConcatExpr>(e)) {
    // skips right part
    if (index >= ce->getRight()->bits())
      return createExtract(ce->getLeft(), index - ce->getRight()->bits(), bits);

    // skips left part
    if (index + bits <= ce->getRight()->bits())
      return createExtract(ce->getRight(), index, bits);

    // E(C(C_0,y)) ==> C(E(C_0), E(y))
    if (ce->getLeft()->isConstant()) {
      return createConcat(
          createExtract(ce->getLeft(), 0, bits - ce->getRight()->bits() + index),
          createExtract(ce->getRight(), index, ce->getRight()->bits() - index));
    }
  }
  else if (auto ee = castAs<ExtExpr>(e)) {
    // E(Ext(x), i, b) && len(x) >= i + b == E(x, i, b)
    if (ee->expr()->bits() >= index + bits)
      return createExtract(ee->expr(), index, bits);

    // E(ZExt(x), i, b) && len(x) < i == 0
    if (ee->kind() == ZExt
        && index >= ee->expr()->bits())
      return createConstant(0, bits);
  }
  else if (auto ee = castAs<ExtractExpr>(e)) {
    // E(E(x, i1, b1), i2, b2) == E(x, i1 + i2, b2)
    return createExtract(ee->expr(), ee->index() + index, bits);
  }

  if (index == 0 && e->bits() == bits)
    return e;

  if (e->kind() == ZExt && e->bits() > index + bits && e->getChild(0)->bits() < index + bits) {
    e = ExprBuilder::createZExt(e->getChild(0), index + bits);
  }

  if (auto ite_e = castAs<IteExpr>(e)) {
    if (auto const_true = castAs<ConstantExpr>(ite_e->getChild(1))) {
      if (auto const_false = castAs<ConstantExpr>(ite_e->getChild(2))) {
        return createIte(ite_e->getChild(0), createExtract(const_true, index, bits), createExtract(const_false, index, bits));
      }
    }
  }

  return ExprBuilder::createExtract(e, index, bits);
}

ExprRef CommonSimplifyExprBuilder::createZExt(
    ExprRef e, UINT32 bits) {
  // allow shrinking
  if (e->bits() > bits)
    return createExtract(e, 0, bits);
  if (e->bits() == bits)
    return e;

  if (auto ite_e = castAs<IteExpr>(e)) {
    if (auto const_true = castAs<ConstantExpr>(ite_e->getChild(1))) {
      if (auto const_false = castAs<ConstantExpr>(ite_e->getChild(2))) {
        return createIte(ite_e->getChild(0), createZExt(const_true, bits), createZExt(const_false, bits));
      }
    }
  }
  return ExprBuilder::createZExt(e, bits);
}

ExprRef CommonSimplifyExprBuilder::createIte(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false) {
  if (auto const_true = castAs<ConstantExpr>(expr_true)) {
    if (auto const_false = castAs<ConstantExpr>(expr_false)) {
      if (const_true->value() == const_false->value()) {
        return expr_true;
      }
    }
  }
  return ExprBuilder::createIte(expr_cond, expr_true, expr_false);
}

ExprRef CommonSimplifyExprBuilder::createAdd(ExprRef l, ExprRef r)
{
  if (isZero(l))
    return r;

  return ExprBuilder::createAdd(l, r);
}

ExprRef CommonSimplifyExprBuilder::createMul(ExprRef l, ExprRef r) {
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  // 0 * X ==> 0
  if (isZero(l))
    return l;

  // 1 * X ==> X
  if (isOne(l))
    return r;

  return ExprBuilder::createMul(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyAnd(ExprRef l, ExprRef r) {
  // l & 0 ==> 0
  if (isZero(l))
    return l;

  // l & 11...1b ==> l;
  if (isAllOnes(l))
    return r;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createAnd(ExprRef l, ExprRef r)
{
  if (ExprRef simplified = simplifyAnd(l, r))
    return simplified;

  // 0x00ff0000  & 0xaabbccdd = 0x00bb0000
  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyAnd(l_left, r_left)) {
        return createConcat(
            and_left,
            createAnd(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    } 
    
    if (r->kind() != Constant && l->bits() <= 64){
      ADDRINT lval = const_l->value().getLimitedValue();
      switch(lval) {
        case 0xFFFFFFFF: {
          if (l->bits() == 32) return r;
          return createConcat(createConstant(0, l->bits() - 32), createExtract(r, 0, 32));
        }
        case 0xFFFFFF00: {
          ExprRef e = createConcat(createExtract(r, 8, 24), createConstant(0, 8));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0xF0000000: {
          ExprRef e = createConcat(createExtract(r, 28, 4), createConstant(0, 28));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0xFF00000: {
          ExprRef e = createConcat(createExtract(r, 20, 8), createConstant(0, 20));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x1000000: {
          ExprRef e = createConcat(createExtract(r, 25, 1), createConstant(0, 25));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0xFFFF: {
          ExprRef e = createExtract(r, 0, 16);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x8000: {
          ExprRef e = createConcat(createExtract(r, 15, 1), createConstant(0, 15));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x4000: {
          ExprRef e = createConcat(createExtract(r, 14, 1), createConstant(0, 14));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x2000: {
          ExprRef e = createConcat(createExtract(r, 13, 1), createConstant(0, 13));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x1000: {
          ExprRef e = createConcat(createExtract(r, 12, 1), createConstant(0, 12));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x800: {
          ExprRef e = createConcat(createExtract(r, 11, 1), createConstant(0, 11));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x400: {
          ExprRef e = createConcat(createExtract(r, 10, 1), createConstant(0, 10));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x200: {
          ExprRef e = createConcat(createExtract(r, 9, 1), createConstant(0, 9));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x1FF: {
          ExprRef e = createExtract(r, 0, 9);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x100: {
          ExprRef e = createConcat(createExtract(r, 8, 1), createConstant(0, 8));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0xFF: {
          ExprRef e = createExtract(r, 0, 8);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0xFE: {
          ExprRef e = createConcat(createExtract(r, 1, 7), createConstant(0, 1));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x80: {
          ExprRef e = createConcat(createExtract(r, 7, 1), createConstant(0, 7));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x40: {
          ExprRef e = createConcat(createExtract(r, 6, 1), createConstant(0, 6));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x20: {
          ExprRef e = createConcat(createExtract(r, 5, 1), createConstant(0, 5));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x10: {
          ExprRef e = createConcat(createExtract(r, 4, 1), createConstant(0, 4));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x8: {
          ExprRef e = createConcat(createExtract(r, 3, 1), createConstant(0, 3));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x7: {
          ExprRef e = createExtract(r, 0, 3);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x4: {
          ExprRef e = createConcat(createExtract(r, 2, 1), createConstant(0, 2));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x3: {
          ExprRef e = createExtract(r, 0, 2);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x2: {
          ExprRef e = createConcat(createExtract(r, 1, 1), createConstant(0, 1));
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        case 0x1: {
          ExprRef e = createExtract(r, 0, 1);
          if (l->bits() > e->bits()) e = createConcat(createConstant(0, l->bits() - e->bits()), e);
          return e;
        }
        default: {
          // printf("\nAND: l=%s r=%s\n\n", l->toString().c_str(), r->toString().c_str());
          break;
        }
      }
    }
  }

  return ExprBuilder::createAnd(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyOr(ExprRef l, ExprRef r) {
  // 0 | X ==> 0
  if (isZero(l))
    return r;

  // 111...1b | X ==> 111...1b
  if (isAllOnes(l))
    return l;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createOr(ExprRef l, ExprRef r) {
  if (ExprRef simplified = simplifyOr(l, r))
    return simplified;

  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyOr(l_left, r_left)) {
        return createConcat(
            and_left,
            createOr(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    }
  }

  // Or(A | 0, Zext(B)) where bits(0) == bits(B) -> Concat(A, B)
  if (auto concat_l = castAs<ConcatExpr>(l)) {
    if (auto const_l_child2 = castAs<ConstantExpr>(l->getChild(1))) {
      if (const_l_child2->isZero()) {
        if (auto zext_r = castAs<ZExtExpr>(r)) {
          if (zext_r->getChild(0)->bits() == const_l_child2->bits()) {
            return createConcat(l->getChild(0), zext_r->getChild(0));
          }
        }
      }
    }
  }

  // Or(Concat(Zext(A), C), B | 0) where bits(0) == (bits(A) + bits(C)) -> Concat(B, A, C)
  if (auto concat_r = castAs<ConcatExpr>(r)) {
    if (auto const_r_child2 = castAs<ConstantExpr>(r->getChild(1))) {
      if (const_r_child2->isZero()) {
        if (auto concat_l = castAs<ConcatExpr>(l)) {
          if (auto zext_l_child1 = castAs<ZExtExpr>(l->getChild(0))) {
            if (zext_l_child1->getChild(0)->bits() + l->getChild(1)->bits() == const_r_child2->bits()) {
              ExprRef e = createConcat(zext_l_child1->getChild(0), l->getChild(1));
              e = createConcat(r->getChild(0), e);
              return e;
            }
          }
        }
      }
    }
  }

  if (auto ite = castAs<IteExpr>(l)) {
    if (auto const_r = castAs<ConstantExpr>(r)) {
      if (auto ite_child1 = castAs<ConstantExpr>(ite->getChild(1))) {
        if (auto ite_child2 = castAs<ConstantExpr>(ite->getChild(2))) {
          return createIte(ite->getChild(0), createOr(ite->getChild(1), const_r), createOr(ite->getChild(2), const_r));
        }
      }
    }
  }

  if (auto ite = castAs<IteExpr>(r)) {
    if (auto const_l = castAs<ConstantExpr>(l)) {
      if (auto ite_child1 = castAs<ConstantExpr>(ite->getChild(1))) {
        if (auto ite_child2 = castAs<ConstantExpr>(ite->getChild(2))) {
          return createIte(ite->getChild(0), createOr(ite->getChild(1), const_l), createOr(ite->getChild(2), const_l));
        }
      }
    }
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef CommonSimplifyExprBuilder::simplifyXor(ExprRef l, ExprRef r) {
  // 0 ^ X ==> X
  if (isZero(l))
    return r;

  return NULL;
}

ExprRef CommonSimplifyExprBuilder::createXor(ExprRef l, ExprRef r) {
  if (ExprRef simplified = simplifyXor(l, r))
    return simplified;

  if (auto const_l = castAs<ConstantExpr>(l)) {
    if (auto concat_r = castAs<ConcatExpr>(r)) {
      ExprRef r_left = concat_r->getLeft();
      ExprRef r_right = concat_r->getRight();
      ExprRef l_left = createExtract(l, r_right->bits(), r_left->bits());

      if (ExprRef and_left = simplifyXor(l_left, r_left)) {
        return createConcat(
            and_left,
            createXor(
              createExtract(l, 0,  r_right->bits()),
              r_right));
      }
    }
  }

  return ExprBuilder::createXor(l, r);
}

ExprRef CommonSimplifyExprBuilder::createSExt(ExprRef e, UINT32 bits) {
  // SExt(x, ITE(a, A, B)) -> ITE(a, SExt(x, A), SExt(x, B))
  if (auto ite_e = castAs<IteExpr>(e)) {
    if (auto const_true = castAs<ConstantExpr>(ite_e->getChild(1))) {
      if (auto const_false = castAs<ConstantExpr>(ite_e->getChild(2))) {
        return createIte(ite_e->getChild(0), createSExt(const_true, bits), createSExt(const_false, bits));
      }
    }
  }
  return ExprBuilder::createSExt(e, bits);
}

ExprRef CommonSimplifyExprBuilder::createShl(ExprRef l, ExprRef r) {
  if (isZero(l))
    return l;

  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    ADDRINT rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;

    // l << larger_than_l_size == 0
    if (rval >= l->bits())
      return createConstant(0, l->bits());

    // from z3: (bvshl x k) -> (concat (extract [n-1-k:0] x) bv0:k)
    // but byte granuality
    if (rval % CHAR_BIT == 0) {
      ExprRef zero = createConstant(0, rval);
      ExprRef partial = createExtract(l, 0, l->bits() - rval);
      return createConcat(partial, zero);
    }
  
    if (auto ite_l = castAs<IteExpr>(l)) {
      return createIte(ite_l->getChild(0), createShl(ite_l->getChild(1), r), createShl(ite_l->getChild(2), r));
    }
  }

  return ExprBuilder::createShl(l, r);
}

ExprRef CommonSimplifyExprBuilder::createLShr(ExprRef l, ExprRef r) {
  if (isZero(l))
    return l;

  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    ADDRINT rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;

    // l << larger_than_l_size == 0
    if (rval >= l->bits())
      return createConstant(0, l->bits());

    // from z3: (bvlshr x k) -> (concat bv0:k (extract [n-1:k] x))
    // but byte granuality
    if (rval % CHAR_BIT == 0) {
      ExprRef zero = createConstant(0, rval);
      ExprRef partial = createExtract(l, rval, l->bits() - rval);
      return createConcat(zero, partial);
    }
  }

  return ExprBuilder::createLShr(l, r);
}

ExprRef CommonSimplifyExprBuilder::createAShr(ExprRef l, ExprRef r) {
  if (ConstantExprRef ce_r = castAs<ConstantExpr>(r)) {
    ADDRINT rval = ce_r->value().getLimitedValue();
    if (rval == 0)
      return l;

    // AShr(0 | A, x) -> 0 | Extract(A, x, len(A) - x)
    if (auto concat_l = castAs<ConcatExpr>(l)) {
      if (auto constant_l_child1 = castAs<ConstantExpr>(concat_l->getChild(0))) {
        if (constant_l_child1->isZero()) {
          ExprRef e = nullptr;
          if (concat_l->getChild(1)->bits() > rval) {
            e = createExtract(concat_l->getChild(1), rval, concat_l->getChild(1)->bits() - rval);
            e = createConcat(createConstant(0, rval), e);
          } else {
            e = createConstant(0, l->bits());
          }
          return e;
        }
      }
    }
  }
  return ExprBuilder::createAShr(l, r);
}

ExprRef CommonSimplifyExprBuilder::createEqual(ExprRef l, ExprRef r) {
  NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (auto be_l = castAs<BoolExpr>(l))
    return (be_l->value()) ? r : createLNot(r);

  if (auto ce_l = castAs<ConstantExpr>(l)) {
    if (ce_l->isZero()) {
      if (auto concat_r = castAs<ConcatExpr>(r)) {
        if (auto concat_child1 = castAs<ConstantExpr>(r->getChild(0))) {
          if (!concat_child1->isZero())
            return createFalse();
        }
        if (auto concat_child2 = castAs<ConstantExpr>(r->getChild(1))) {
          if (!concat_child2->isZero())
            return createFalse();
        }
      }
    }
  }

  // Equal(0x0, ITE(C, 0x1, 0x0)) -> !C
  if (auto ce_l = castAs<ConstantExpr>(l)) {
    if (auto ite_r = castAs<IteExpr>(r)) {
      if (auto ite_child_t = castAs<ConstantExpr>(r->getChild(1))) {
        if (auto ite_child_f = castAs<ConstantExpr>(r->getChild(2))) {
          if (ce_l->isZero() && ite_child_t->isOne() && ite_child_f->isZero()) {
            return createLNot(ite_r->getChild(0));
          }
        }
      }    
    }  
  }

  return ExprBuilder::createEqual(l, r);
}

ExprRef ConstantFoldingExprBuilder::createDistinct(ExprRef l, ExprRef r) {
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    QSYM_ASSERT(l->bits() == r->bits());
    return createBool(ce_l->value() != ce_r->value());
  }

  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL) {
    return createBool(be0->value() != be1->value());
  }

  return ExprBuilder::createDistinct(l, r);
}

ExprRef ConstantFoldingExprBuilder::createEqual(ExprRef l, ExprRef r) {
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    QSYM_ASSERT(l->bits() == r->bits());
    return createBool(ce_l->value() == ce_r->value());
  }

  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() == be1->value());

  return ExprBuilder::createEqual(l, r);
}

ExprRef ConstantFoldingExprBuilder::createLAnd(ExprRef l, ExprRef r) {
  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() && be1->value());
  else
    return ExprBuilder::createLAnd(l, r);
}

ExprRef ConstantFoldingExprBuilder::createLOr(ExprRef l, ExprRef r) {
  BoolExprRef be0 = castAs<BoolExpr>(l);
  BoolExprRef be1 = castAs<BoolExpr>(r);

  if (be0 != NULL && be1 != NULL)
    return createBool(be0->value() || be1->value());
  else
    return ExprBuilder::createLOr(l, r);
}

ExprRef ConstantFoldingExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(l, r) && l == constant && r == constant  => l << r_bits | r
  ConstantExprRef ce_l = castAs<ConstantExpr>(l);
  ConstantExprRef ce_r = castAs<ConstantExpr>(r);

  if (ce_l != NULL && ce_r != NULL) {
    UINT32 bits = ce_l->bits() + ce_r->bits();
    llvm::APInt lval = ce_l->value().zext(bits);
    llvm::APInt rval = ce_r->value().zext(bits);
    llvm::APInt res = (lval << ce_r->bits()) | rval;
    return createConstant(res, bits);
  }
  else
    return ExprBuilder::createConcat(l, r);
}

ExprRef ConstantFoldingExprBuilder::createIte(ExprRef expr_cond,
    ExprRef expr_true, ExprRef expr_false) {
  if (auto be = castAs<BoolExpr>(expr_cond)) {
    if (be->value())
      return expr_true;
    else
      return expr_false;
  }

  return ExprBuilder::createIte(expr_cond, expr_true, expr_false);
}

ExprRef ConstantFoldingExprBuilder::createExtract(
    ExprRef e, UINT32 index, UINT32 bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    llvm::APInt v = ce->value().lshr(index);
    v = v.zextOrTrunc(bits);
    return createConstant(v, bits);
  }
  else
    return ExprBuilder::createExtract(e, index, bits);
}

ExprRef ConstantFoldingExprBuilder::createZExt(ExprRef e, UINT32 bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    return createConstant(ce->value().zext(bits), bits);
  }
  else
    return ExprBuilder::createZExt(e, bits);
}

ExprRef ConstantFoldingExprBuilder::createSExt(ExprRef e, UINT32 bits) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e)) {
    return createConstant(ce->value().sext(bits), bits);
  }
  else
    return ExprBuilder::createSExt(e, bits);
}

ExprRef ConstantFoldingExprBuilder::createNeg(ExprRef e) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return createConstant(-ce->value(), ce->bits());
  else
    return ExprBuilder::createNeg(e);
}

ExprRef ConstantFoldingExprBuilder::createNot(ExprRef e) {
  if (ConstantExprRef ce = castAs<ConstantExpr>(e))
    return createConstant(~ce->value(), ce->bits());
  else
    return ExprBuilder::createNot(e);
}

ExprRef ConstantFoldingExprBuilder::createLNot(ExprRef e) {
  if (BoolExprRef be = castAs<BoolExpr>(e))
    return createBool(!be->value());
  else
    return ExprBuilder::createLNot(e);
}

ExprRef SymbolicExprBuilder::createConcat(ExprRef l, ExprRef r) {
  // C(l, C(x, y)) && l, x == constant => C(l|x, y)
  if (auto ce = castAs<ConcatExpr>(r)) {
    ConstantExprRef ce_l = castAs<ConstantExpr>(l);
    ConstantExprRef ce_x = castAs<ConstantExpr>(ce->getLeft());
    if (ce_l != NULL && ce_x != NULL)
      return createConcat(createConcat(ce_l, ce_x), ce->getRight());
  }

  // C(C(x ,y), z) => C(x, C(y, z))
  if (auto ce = castAs<ConcatExpr>(l)) {
    return createConcat(l->getLeft(),
        createConcat(l->getRight(), r));
  }

  return ExprBuilder::createConcat(l, r);
}

ExprRef SymbolicExprBuilder::createExtract(ExprRef op, UINT32 index, UINT32 bits) {
  // Only byte-wise simplification
  if (index == 0
      && bits % 8 == 0
      && canEvaluateTruncated(op, bits)) {
      if (ExprRef e = evaluateInDifferentType(this, op, index, bits))
        return e;
  }
  return ExprBuilder::createExtract(op, index, bits);
}

ExprRef SymbolicExprBuilder::simplifyExclusiveExpr(ExprRef l, ExprRef r) {
  // From z3
  // (bvor (concat x #x00) (concat #x00 y)) --> (concat x y)
  // (bvadd (concat x #x00) (concat #x00 y)) --> (concat x y)

  for (UINT i = 0; i < l->bits(); i++)
    if (!isZeroBit(l, i) && !isZeroBit(r, i))
      return NULL;

  std::list<ExprRef> exprs;
  UINT32 i = 0;
  while (i < l->bits()) {
    UINT32 prev = i;
    while (i < l->bits() && isZeroBit(l, i))
      i++;
    if (i != prev)
      exprs.push_front(createExtract(r, prev, i - prev));
    prev = i;
    while (i < r->bits() && isZeroBit(r, i))
      i++;
    if (i != prev)
      exprs.push_front(createExtract(l, prev, i - prev));
  }

  return ExprBuilder::createConcat(exprs);
}

ExprRef SymbolicExprBuilder::createAdd(ExprRef l, ExprRef r) {
  if (ExprRef e = simplifyExclusiveExpr(l, r))
    return e;

  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createAdd(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      QSYM_ASSERT(nce_l != NULL);
      return createAdd(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createAdd(ConstantExprRef l, NonConstantExprRef r) {
  switch (r->kind()) {
    case Add: {
      // C_0 + (C_1 + X) ==> (C_0 + C_1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createAdd(l, CE), r->getSecondChild());
      // C_0 + (X + C_1) ==> (C_0 + C_1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createAdd(l, CE), r->getFirstChild());
      break;
    }

    case Sub: {
      // C_0 + (C_1 - X) ==> (C_0 + C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createSub(createAdd(l, CE), r->getSecondChild());
      // C_0 + (X - C_1) ==> (C_0 - C1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createSub(l, CE), r->getFirstChild());
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createAdd(NonConstantExprRef l, NonConstantExprRef r) {
  if (l == r) {
    // l + l ==> 2 * l
    ExprRef two = createConstant(2, l->bits());
    return createMul(two, l);
  }

  switch (l->kind()) {
    default: break;
    case Add:
    case Sub: {
      // (X + Y) + Z ==> Z + (X + Y)
      // Or (X - Y) + Z ==> Z + (X - Y)
      std::swap(l, r);
    }
  }

  switch (r->kind()) {
    case Add: {
      // X + (C_0 + Y) ==> C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(CE, createAdd(l, r->getSecondChild()));
      // X + (Y + C_0) ==> C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(CE, createAdd(l, r->getFirstChild()));
      break;
    }

    case Sub: {
      // X + (C_0 - Y) ==> C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(CE, createSub(l, r->getSecondChild()));
      // X + (Y - C_0) ==> -C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createNeg(CE), createAdd(l, r->getFirstChild()));
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createAdd(l, r);
}

ExprRef SymbolicExprBuilder::createSub(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createSub(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      QSYM_ASSERT(nce_l != NULL);
      return createSub(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createSub(ConstantExprRef l, NonConstantExprRef r) {
  switch (r->kind()) {
    case Add: {
      // C_0 - (C_1 + X) ==> (C_0 - C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createSub(createSub(l, CE), r->getSecondChild());
      // C_0 - (X + C_1) ==> (C_0 - C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createSub(createSub(l, CE), r->getFirstChild());
      break;
    }

    case Sub: {
      // C_0 - (C_1 - X) ==> (C_0 - C1) + X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild())) {
        return createAdd(createSub(l, CE), r->getSecondChild());
      }
      // C_0 - (X - C_1) ==> (C_0 + C1) - X
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild())) {
        return createSub(createAdd(l, CE), r->getFirstChild());
      }
      break;
    }
    default:
      break;
  }

  return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createSub(
    NonConstantExprRef l,
    NonConstantExprRef r) {
  // X - X ==> 0
  if (l == r)
    return createConstant(0, l->bits());

  switch (l->kind()) {
    default: break;
    case Add:
      if (l->getChild(0)->isConstant()) {
        // (C + Y) - Z ==> C + (Y - Z)
        return createAdd(l->getChild(0),
            createSub(l->getChild(1), r));
      }
    case Sub: {
      if (l->getChild(0)->isConstant()) {
        // (C - Y) - Z ==> C - (Y + Z)
        return createSub(l->getChild(0),
            createAdd(l->getChild(1), r));
      }
    }
  }

  switch (r->kind()) {
    case Add: {
      // X - (C_0 + Y) ==> -C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createNeg(CE), createSub(l, r->getSecondChild()));
      // X - (Y + C_0) ==> -C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(createNeg(CE), createSub(l, r->getFirstChild()));
      break;
    }

    case Sub: {
      // X - (C_0 - Y) ==> -C_0 + (X + Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getFirstChild()))
        return createAdd(createNeg(CE), createAdd(l, r->getSecondChild()));
      // X - (Y - C_0) ==> C_0 + (X - Y)
      if (ConstantExprRef CE = castAs<ConstantExpr>(r->getSecondChild()))
        return createAdd(CE, createSub(l, r->getFirstChild()));
      break;
    }
    default:
      break;
  }
  return ExprBuilder::createSub(l, r);
}

ExprRef SymbolicExprBuilder::createMul(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createMul(ce_l, nce_r);
  }

  return ExprBuilder::createMul(l, r);
}

ExprRef SymbolicExprBuilder::createMul(ConstantExprRef l, NonConstantExprRef r) {
  // C_0 * (C_1 * x) ==> (C_0 * C_1) * x
  if (auto me = castAs<MulExpr>(r)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(r->getLeft())) {
      return createMul(createMul(l, ce), r->getRight());
    }
  }

  // C_0 * (C_1 + x) ==> C_0 * C_1 + C_0 * x
  if (auto ae = castAs<AddExpr>(r)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(r->getLeft())) {
      return createAdd(createMul(l, ce), createMul(l, r->getRight()));
    }
  }

  return ExprBuilder::createMul(l, r);
}

ExprRef SymbolicExprBuilder::createSDiv(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
    if (ConstantExprRef ce_r = castAs<ConstantExpr>(r))
      return createSDiv(nce_l, ce_r);
  }

  return ExprBuilder::createSDiv(l, r);
}

ExprRef SymbolicExprBuilder::createSDiv(NonConstantExprRef l, ConstantExprRef r) {
  // x /s -1 = -x
  if (r->isAllOnes())
    return createNeg(l);

  // SExt(x) /s y && x->bits() >= y->getActiveBits() ==> SExt(x /s y)
  // Only works when y != -1, but already handled by the above statement
  if (auto sext_l = castAs<SExtExpr>(l)) {
    ExprRef x = sext_l->expr();
    if (x->bits() >= r->getActiveBits()) {
      return createSExt(
              createSDiv(x,
                createExtract(r, 0, x->bits())),
              l->bits());
    }
  }

  // TODO: add overflow check
  // (x / C_0) / C_1 = (x / (C_0 * C_1))
  if (auto se = castAs<SDivExpr>(l)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(l->getRight())) {
      return createSDiv(l->getLeft(), createMul(ce, r));
    }
  }
  return ExprBuilder::createSDiv(l, r);
}

ExprRef SymbolicExprBuilder::createUDiv(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
    if (ConstantExprRef ce_r = castAs<ConstantExpr>(r))
      return createUDiv(nce_l, ce_r);
  }

  return ExprBuilder::createUDiv(l, r);
}

ExprRef SymbolicExprBuilder::createUDiv(NonConstantExprRef l, ConstantExprRef r) {
  // C(0, x) / y && y->getActiveBits() <= x->bits()
  // == C(0, x/E(y, 0, x->bits()))
  if (auto ce = castAs<ConcatExpr>(l)) {
    ExprRef ce_l = ce->getLeft();
    ExprRef ce_r = ce->getRight();
    if (ce_l->isZero()) {
      if (r->getActiveBits() <= ce_r->bits()) {
        ExprRef e = createConcat(
            ce_l,
            createUDiv(
              ce_r,
              createExtract(r, 0, ce_r->bits())));
        return e;
      }
    }
  }

  // TODO: add overflow check
  // (x / C_0) / C_1 = (x / (C_0 * C_1))
  if (auto se = castAs<UDivExpr>(l)) {
    if (ConstantExprRef ce = castAs<ConstantExpr>(l->getRight())) {
      return createUDiv(l->getLeft(), createMul(ce, r));
    }
  }
  return ExprBuilder::createUDiv(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createAnd(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      QSYM_ASSERT(nce_l != NULL);
      return createAnd(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(ConstantExprRef l, NonConstantExprRef r) {
  return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createAnd(NonConstantExprRef l, NonConstantExprRef r) {
  // A & A  ==> A
  if (l == r)
    return l;

  // C(x, y) & C(w, v) ==> C(x & w, y & v)
  if (auto ce_l = castAs<ConcatExpr>(l)) {
    if (auto ce_r = castAs<ConcatExpr>(r)) {
      if (ce_l->getLeft()->bits() == ce_r->getLeft()->bits()) {
        // right bits are same, because it is binary operation
        return createConcat(
            createAnd(l->getLeft(), r->getLeft()),
            createAnd(l->getRight(), r->getRight()));
      }
    }
  }
  return ExprBuilder::createAnd(l, r);
}

ExprRef SymbolicExprBuilder::createOr(ExprRef l, ExprRef r) {
 if (ExprRef e = simplifyExclusiveExpr(l, r))
    return e;

  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (ConstantExprRef ce_l = castAs<ConstantExpr>(l))
      return createOr(ce_l, nce_r);
    else {
      NonConstantExprRef nce_l = castAs<NonConstantExpr>(l);
      QSYM_ASSERT(nce_l != NULL);
      return createOr(nce_l, nce_r);
    }
  }
  else
    return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createOr(ConstantExprRef l, NonConstantExprRef r) {
  if (auto ce = castAs<ConcatExpr>(r)) {
    // C_0 | C(x, y) ==> C(C_0 | x, C_0 | y)
    // TODO: only for constant case
    return createConcat(
        createOr(
          createExtract(l, ce->getRight()->bits(), ce->getLeft()->bits()),
          ce->getLeft()),
        createOr(
          createExtract(l, 0, ce->getRight()->bits()),
          ce->getRight()));
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createOr(NonConstantExprRef l, NonConstantExprRef r) {
  // A | A = A
  if (l == r)
    return l;

  // C(x, y) & C(w, v) == C(x | w, y | v)
  if (auto ce_l = castAs<ConcatExpr>(l)) {
    if (auto ce_r = castAs<ConcatExpr>(r)) {
      if (ce_l->getLeft()->bits() == ce_r->getLeft()->bits()) {
        // right bits are same, because it is binary operation
        return createConcat(
            createOr(l->getLeft(), r->getLeft()),
            createOr(l->getRight(), r->getRight()));
      }
    }
  }

  return ExprBuilder::createOr(l, r);
}

ExprRef SymbolicExprBuilder::createXor(ExprRef l, ExprRef r) {
  if (NonConstantExprRef nce_r = castAs<NonConstantExpr>(r)) {
    if (NonConstantExprRef nce_l = castAs<NonConstantExpr>(l)) {
      return createXor(nce_l, nce_r);
    }
  }

  return ExprBuilder::createXor(l, r);
}

ExprRef SymbolicExprBuilder::createXor(NonConstantExprRef l, NonConstantExprRef r) {
  if (l == r)
    return createConstant(0, l->bits());
  else
    return ExprBuilder::createXor(l, r);
}

ExprRef SymbolicExprBuilder::createEqual(ExprRef l, ExprRef r) {
  if (l == r)
    return createTrue();

  return ExprBuilder::createEqual(l, r);
}

ExprRef SymbolicExprBuilder::createDistinct(ExprRef l, ExprRef r) {
  return createLNot(createEqual(l, r));
}

ExprRef SymbolicExprBuilder::createLOr(ExprRef l, ExprRef r) {
  if (auto BE_L = castAs<BoolExpr>(l))
    return BE_L->value() ? createTrue() : r;

  if (auto BE_R = castAs<BoolExpr>(r))
    return BE_R->value() ? createTrue() : l;

  return ExprBuilder::createLOr(l, r);
}

ExprRef SymbolicExprBuilder::createLAnd(ExprRef l, ExprRef r) {
  if (auto BE_L = castAs<BoolExpr>(l))
    return BE_L->value() ? r : createFalse();

  if (auto BE_R = castAs<BoolExpr>(r))
    return BE_R->value() ? l : createFalse();

  return ExprBuilder::createLAnd(l, r);
}

ExprRef SymbolicExprBuilder::createLNot(ExprRef e) {
  if (auto BE = castAs<BoolExpr>(e))
    return createBool(!BE->value());
  if (auto NE = castAs<LNotExpr>(e))
    return NE->expr();
  return ExprBuilder::createLNot(e);
}

ExprRef SymbolicExprBuilder::createIte(
    ExprRef expr_cond,
    ExprRef expr_true,
    ExprRef expr_false) {
  if (auto BE = castAs<BoolExpr>(expr_cond))
    return BE->value() ? expr_true : expr_false;
  if (auto NE = castAs<LNotExpr>(expr_cond))
    return createIte(NE->expr(), expr_false, expr_true);
  return ExprBuilder::createIte(expr_cond, expr_true, expr_false);
}

ExprBuilder* PruneExprBuilder::create() {
  ExprBuilder* base = new BaseExprBuilder();
  ExprBuilder* commu = new CommutativeExprBuilder();
  ExprBuilder* common = new CommonSimplifyExprBuilder();
  ExprBuilder* const_folding = new ConstantFoldingExprBuilder();
  ExprBuilder* symbolic = new SymbolicExprBuilder();
  ExprBuilder* cache = new CacheExprBuilder();
  ExprBuilder* fuzz = new PruneExprBuilder();

  // commu -> symbolic -> common -> constant folding -> fuzz -> cache -> base
  commu->setNext(symbolic);
  symbolic->setNext(common);
  common->setNext(const_folding);
  const_folding->setNext(fuzz);
  fuzz->setNext(cache);
  cache->setNext(base);
  return commu;
}

{CODEGEN}

} // namespace qsym
