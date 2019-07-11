//===--- EnumPayload.cpp - Payload management for 'enum' Types ------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#include "APInt.h"
#include "EnumPayload.h"
#include "Explosion.h"
#include "GenEnum.h"
#include "IRGenModule.h"
#include <map>

using namespace swift;
using namespace irgen;

// FIXME: Everything here brazenly assumes little-endian-ness.

static llvm::Value *forcePayloadValue(EnumPayload::LazyValue &value) {
  if (auto v = value.dyn_cast<llvm::Value *>())
    return v;
  
  auto null = llvm::Constant::getNullValue(value.dyn_cast<llvm::Type*>());
  value = null;
  return null;
}

static llvm::Type *getPayloadType(EnumPayload::LazyValue value) {
  if (auto t = value.dyn_cast<llvm::Type *>())
    return t;
  
  return value.dyn_cast<llvm::Value *>()->getType();
}

EnumPayload EnumPayload::zero(IRGenModule &IGM, EnumPayloadSchema schema) {
  // We don't need to create any values yet; they can be filled in when
  // real values are inserted.
  EnumPayload result;
  schema.forEachType(IGM, [&](llvm::Type *type) {
    result.PayloadValues.push_back(type);
  });
  return result;
}

EnumPayload EnumPayload::fromBitPattern(IRGenModule &IGM,
                                        const APInt &bitPattern,
                                        EnumPayloadSchema schema) {
  auto maskReader = APIntReader(bitPattern, IGM.Triple.isLittleEndian());

  EnumPayload result;
  schema.forEachType(IGM, [&](llvm::Type *type) {
    unsigned bitSize = IGM.DataLayout.getTypeSizeInBits(type);

    llvm::IntegerType *intTy
      = llvm::IntegerType::get(IGM.getLLVMContext(), bitSize);

    // Take some bits off of the bottom of the pattern.
    auto bits = maskReader.read(bitSize);
    auto val = llvm::ConstantInt::get(intTy, bits);
    if (val->getType() != type) {
      if (type->isPointerTy())
        val = llvm::ConstantExpr::getIntToPtr(val, type);
      else
        val = llvm::ConstantExpr::getBitCast(val, type);
    }

    result.PayloadValues.push_back(val);
  });

  return result;
}

unsigned EnumPayload::sizeInBits(const IRGenFunction &IGF) const {
  unsigned size = 0U;
  for (const auto &pv : PayloadValues) {
    size += IGF.IGM.DataLayout.getTypeSizeInBits(getPayloadType(pv));
    assert(size % 8 == 0);
  }
  return size;
}

// Fn: void(LazyValue &payloadValue, unsigned payloadBitWidth,
//          unsigned payloadValueOffset, unsigned valueBitWidth,
//          unsigned valueOffset)
template<typename Fn>
static void withValueInPayload(IRGenFunction &IGF,
                               const EnumPayload &payload,
                               llvm::Type *valueType,
                               int numBitsUsedInValue,
                               unsigned payloadOffset,
                               Fn &&f) {
  auto &DataLayout = IGF.IGM.DataLayout;
  int valueTypeBitWidth = DataLayout.getTypeSizeInBits(valueType);
  int valueBitWidth =
      numBitsUsedInValue < 0 ? valueTypeBitWidth : numBitsUsedInValue;
  assert(numBitsUsedInValue <= valueTypeBitWidth);

  // Find the elements we need to touch.
  // TODO: Linear search through the payload elements is lame.
  MutableArrayRef<EnumPayload::LazyValue> payloads = payload.PayloadValues;
  llvm::Type *payloadType;
  int payloadBitWidth;
  int valueOffset = 0, payloadValueOffset = payloadOffset;
  for (;;) {
    payloadType = getPayloadType(payloads.front());
    payloadBitWidth = IGF.IGM.DataLayout.getTypeSizeInBits(payloadType);
    
    // Does this element overlap the area we need to touch?
    if (payloadValueOffset < payloadBitWidth) {
      // See how much of the value we can fit here.
      int valueChunkWidth = payloadBitWidth - payloadValueOffset;
      valueChunkWidth = std::min(valueChunkWidth, valueBitWidth - valueOffset);
    
      f(payloads.front(),
        payloadBitWidth, payloadValueOffset,
        valueTypeBitWidth, valueOffset);
      
      // If we used the entire value, we're done.
      valueOffset += valueChunkWidth;
      if (valueOffset >= valueBitWidth)
        return;
    }
    
    payloadValueOffset = std::max(payloadValueOffset - payloadBitWidth, 0);
    payloads = payloads.slice(1);
  }
}

void EnumPayload::insertValue(IRGenFunction &IGF, llvm::Value *value,
                              unsigned payloadOffset) {
  withValueInPayload(IGF, *this, value->getType(), -1, payloadOffset,
    [&](LazyValue &payloadValue,
        unsigned payloadBitWidth,
        unsigned payloadValueOffset,
        unsigned valueBitWidth,
        unsigned valueOffset) {
      auto payloadType = getPayloadType(payloadValue);
      // See if the value matches the payload type exactly. In this case we
      // don't need to do any work to use the value.
      if (payloadValueOffset == 0 && valueOffset == 0) {
        if (value->getType() == payloadType) {
          payloadValue = value;
          return;
        }
        // If only the width matches exactly, we can still do a bitcast.
        if (payloadBitWidth == valueBitWidth) {
          auto bitcast = IGF.Builder.CreateBitOrPointerCast(value, payloadType);
          payloadValue = bitcast;
          return;
        }
      }
      
      // Select out the chunk of the value to merge with the existing payload.
      llvm::Value *subvalue = value;
      
      auto valueIntTy =
        llvm::IntegerType::get(IGF.IGM.getLLVMContext(), valueBitWidth);
      auto payloadIntTy =
        llvm::IntegerType::get(IGF.IGM.getLLVMContext(), payloadBitWidth);
      auto payloadTy = getPayloadType(payloadValue);
      subvalue = IGF.Builder.CreateBitOrPointerCast(subvalue, valueIntTy);
      int64_t valueShift = valueOffset;
      if (!IGF.IGM.Triple.isLittleEndian()) {
        valueShift = valueBitWidth;
        valueShift -= valueOffset;
        valueShift -= std::min(payloadBitWidth - payloadValueOffset, valueBitWidth - valueOffset);
      }
      assert(valueShift >= 0);
      if (valueShift > 0)
         subvalue = IGF.Builder.CreateLShr(subvalue,
                               llvm::ConstantInt::get(valueIntTy, valueShift));
      subvalue = IGF.Builder.CreateZExtOrTrunc(subvalue, payloadIntTy);
      if (IGF.IGM.Triple.isLittleEndian()) {
        if (payloadValueOffset > 0)
          subvalue = IGF.Builder.CreateShl(subvalue,
                        llvm::ConstantInt::get(payloadIntTy, payloadValueOffset));
      } else {
        if ((valueBitWidth == 32 || valueBitWidth == 16 || valueBitWidth == 8 || valueBitWidth == 1) &&
            payloadBitWidth > (payloadValueOffset + valueBitWidth)) {
          unsigned shiftBitWidth = valueBitWidth;
          if (valueBitWidth == 1) {
            shiftBitWidth = 8;
          }
          subvalue = IGF.Builder.CreateShl(subvalue,
            llvm::ConstantInt::get(payloadIntTy, (payloadBitWidth - shiftBitWidth) - payloadValueOffset));
        }
      }

      // If there hasn't yet been a value stored here, we can use the adjusted
      // value directly.
      if (payloadValue.is<llvm::Type *>()) {
        payloadValue = IGF.Builder.CreateBitOrPointerCast(subvalue, payloadTy);
      }
      // Otherwise, bitwise-or it in, brazenly assuming there are zeroes
      // underneath.
      else {
        // TODO: This creates a bunch of bitcasting noise for non-integer
        // payload fields.
        auto lastValue = payloadValue.get<llvm::Value *>();
        lastValue = IGF.Builder.CreateBitOrPointerCast(lastValue, payloadIntTy);
        lastValue = IGF.Builder.CreateOr(lastValue, subvalue);
        payloadValue = IGF.Builder.CreateBitOrPointerCast(lastValue, payloadTy);
      }
    });
}

static APInt reverseBytes(const APInt &v) {
  assert(v.getBitWidth() % 8 == 0);
  APInt r = v;
  for (unsigned i = 0; i < (v.getBitWidth() / 8U); ++i) {
    APInt b = v.extractBits(8, i * 8);
    r.insertBits(b, v.getBitWidth() - 8 - (i * 8));
  }
  return r;
}

llvm::Value *EnumPayload::extractValue(IRGenFunction &IGF, llvm::Type *type,
                                       unsigned payloadOffset) const {
  assert(payloadOffset % 8 == 0 && "payload offset must be byte aligned");
  unsigned valueSize = IGF.IGM.DataLayout.getTypeSizeInBits(type);
  unsigned payloadSize = sizeInBits(IGF);
  assert(payloadSize >= valueSize + payloadOffset);

  auto mask = APInt::getBitsSet(payloadSize,
                                payloadOffset,
                                payloadOffset + valueSize);
  if (!IGF.IGM.Triple.isLittleEndian()) {
    // Reverse the mask on big-endian systems.
    mask = reverseBytes(mask);
  }
  auto value = emitGatherSpareBits(IGF,
                                   SpareBitVector::fromAPInt(mask),
                                   0,
                                   valueSize);
  if (value->getType() != type) {
    value = IGF.Builder.CreateBitOrPointerCast(value, type);
  }
  return value;
}

EnumPayload EnumPayload::fromExplosion(IRGenModule &IGM,
                                       Explosion &in, EnumPayloadSchema schema){
  EnumPayload result;
  
  schema.forEachType(IGM, [&](llvm::Type *type) {
    auto next = in.claimNext();
    assert(next->getType() == type && "explosion doesn't match payload schema");
    result.PayloadValues.push_back(next);
  });
  
  return result;
}

void EnumPayload::explode(IRGenModule &IGM, Explosion &out) const {
  for (LazyValue &value : PayloadValues) {
    out.add(forcePayloadValue(value));
  }
}

void EnumPayload::packIntoEnumPayload(IRGenFunction &IGF,
                                      EnumPayload &outerPayload,
                                      unsigned bitOffset) const {
  auto &DL = IGF.IGM.DataLayout;
  for (auto &value : PayloadValues) {
    auto v = forcePayloadValue(value);
    outerPayload.insertValue(IGF, v, bitOffset);
    bitOffset += DL.getTypeSizeInBits(v->getType());
  }
}

EnumPayload EnumPayload::unpackFromEnumPayload(IRGenFunction &IGF,
                                        const EnumPayload &outerPayload,
                                        unsigned bitOffset,
                                        EnumPayloadSchema schema) {
  EnumPayload result;
  auto &DL = IGF.IGM.DataLayout;
  schema.forEachType(IGF.IGM, [&](llvm::Type *type) {
    auto v = outerPayload.extractValue(IGF, type, bitOffset);
    result.PayloadValues.push_back(v);
    bitOffset += DL.getTypeSizeInBits(type);
  });
  return result;
}

static llvm::Type *getPayloadStorageType(IRGenModule &IGM,
                                         const EnumPayload &payload) {
  if (payload.StorageType)
    return payload.StorageType;

  if (payload.PayloadValues.size() == 1) {
    payload.StorageType = getPayloadType(payload.PayloadValues.front());
    return payload.StorageType;
  }
  
  SmallVector<llvm::Type *, 2> elementTypes;
  for (auto value : payload.PayloadValues) {
    elementTypes.push_back(getPayloadType(value));
  }
  
  payload.StorageType = llvm::StructType::get(IGM.getLLVMContext(),
                                              elementTypes);
  return payload.StorageType;
}

EnumPayload EnumPayload::load(IRGenFunction &IGF, Address address,
                              EnumPayloadSchema schema) {
  EnumPayload result = EnumPayload::zero(IGF.IGM, schema);
  if (result.PayloadValues.empty())
    return result;
  
  auto storageTy = getPayloadStorageType(IGF.IGM, result);
  address = IGF.Builder.CreateBitCast(address, storageTy->getPointerTo());
  
  if (result.PayloadValues.size() == 1) {
    result.PayloadValues.front() = IGF.Builder.CreateLoad(address);
  } else {
    Size offset(0);
    for (unsigned i : indices(result.PayloadValues)) {
      auto &value = result.PayloadValues[i];
      auto member = IGF.Builder.CreateStructGEP(address, i, offset);
      auto loadedValue = IGF.Builder.CreateLoad(member);
      value = loadedValue;
      offset += Size(IGF.IGM.DataLayout.getTypeAllocSize(loadedValue->getType()));
    }
  }
  
  return result;
}

void EnumPayload::store(IRGenFunction &IGF, Address address) const {
  if (PayloadValues.empty())
    return;

  auto storageTy = getPayloadStorageType(IGF.IGM, *this);
  address = IGF.Builder.CreateBitCast(address, storageTy->getPointerTo());
  
  if (PayloadValues.size() == 1) {
    IGF.Builder.CreateStore(forcePayloadValue(PayloadValues.front()), address);
    return;
  } else {
    Size offset(0);
    for (unsigned i : indices(PayloadValues)) {
      auto &value = PayloadValues[i];
      auto member = IGF.Builder.CreateStructGEP(address, i, offset);
      auto valueToStore = forcePayloadValue(value);
      IGF.Builder.CreateStore(valueToStore, member);
      offset += Size(IGF.IGM.DataLayout
                       .getTypeAllocSize(valueToStore->getType()));
    }
  }
}

void EnumPayload::emitSwitch(IRGenFunction &IGF,
                             const APInt &mask,
                             ArrayRef<std::pair<APInt, llvm::BasicBlock *>> cases,
                             SwitchDefaultDest dflt) const {
  // If there's only one case to test, do a simple compare and branch.
  if (cases.size() == 1) {
    // If the default case is unreachable, don't bother branching at all.
    if (dflt.getInt()) {
      IGF.Builder.CreateBr(cases[0].second);
      return;
    }
  
    assert((~mask & cases[0].first) == 0);
    auto *cmp = emitCompare(IGF, mask, cases[0].first);
    IGF.Builder.CreateCondBr(cmp, cases[0].second, dflt.getPointer());
    return;
  }

  // Otherwise emit a switch statement.
  auto &context = IGF.IGM.getLLVMContext();
  unsigned numBits = mask.countPopulation();
  auto target = emitGatherSpareBits(IGF, SpareBitVector::fromAPInt(mask),
                                    0, numBits);
  auto swi = IGF.Builder.CreateSwitch(target, dflt.getPointer(), cases.size());
  for (auto &c : cases) {
    auto value = llvm::ConstantInt::get(context, gatherBits(mask, c.first));
    swi->addCase(value, c.second);
  }
  assert(IGF.Builder.hasPostTerminatorIP());
}

llvm::Value *
EnumPayload::emitCompare(IRGenFunction &IGF,
                         const APInt &mask,
                         const APInt &value) const {
  // Succeed trivially for an empty payload, or if the payload is masked
  // out completely.
  if (PayloadValues.empty() || mask == 0)
    return llvm::ConstantInt::get(IGF.IGM.Int1Ty, 1U);

  assert((~mask & value) == 0
         && "value has masked out bits set?!");

  auto valueReader = APIntReader(value, IGF.IGM.Triple.isLittleEndian());
  auto maskReader = APIntReader(mask, IGF.IGM.Triple.isLittleEndian());

  auto &DL = IGF.IGM.DataLayout;
  llvm::Value *condition = nullptr;
  for (auto &pv : PayloadValues) {
    auto v = forcePayloadValue(pv);
    unsigned size = DL.getTypeSizeInBits(v->getType());

    // Break off a piece of the mask and value.
    auto maskPiece = maskReader.read(size);
    auto valuePiece = valueReader.read(size);

    // If this piece is zero, it doesn't affect the comparison.
    if (maskPiece == 0)
      continue;
    
    // Apply the mask and test.
    bool isMasked = !maskPiece.isAllOnesValue();
    auto intTy = llvm::IntegerType::get(IGF.IGM.getLLVMContext(), size);
    // Need to bitcast to an integer in order to use 'icmp eq' if the piece
    // isn't already an int or pointer, or in order to apply a mask.
    if (isMasked
        || (!isa<llvm::IntegerType>(v->getType())
            && !isa<llvm::PointerType>(v->getType())))
      v = IGF.Builder.CreateBitOrPointerCast(v, intTy);
    
    if (isMasked) {
      auto maskConstant = llvm::ConstantInt::get(intTy, maskPiece);
      v = IGF.Builder.CreateAnd(v, maskConstant);
    }
    
    llvm::Value *valueConstant = llvm::ConstantInt::get(intTy, valuePiece);
    valueConstant = IGF.Builder.CreateBitOrPointerCast(valueConstant,
                                                       v->getType());
    auto cmp = IGF.Builder.CreateICmpEQ(v, valueConstant);
    if (!condition)
      condition = cmp;
    else
      condition = IGF.Builder.CreateAnd(condition, cmp);
  }
  
  // We should have handled the cases where there are no significant conditions
  // in the early exit.
  assert(condition && "no significant condition?!");
  return condition;
}

void
EnumPayload::emitApplyAndMask(IRGenFunction &IGF, const APInt &mask) {
  // Early exit if the mask has no effect.
  if (mask.isAllOnesValue())
    return;

  auto maskReader = APIntReader(mask, IGF.IGM.Triple.isLittleEndian());

  auto &DL = IGF.IGM.DataLayout;
  for (auto &pv : PayloadValues) {
    auto payloadTy = getPayloadType(pv);
    unsigned size = DL.getTypeSizeInBits(payloadTy);

    // Read a chunk of the mask.
    auto maskPiece = maskReader.read(size);
    
    // If this piece is all ones, it has no effect.
    if (maskPiece.isAllOnesValue())
      continue;

    // If the payload value is vacant, the mask can't change it.
    if (pv.is<llvm::Type *>())
      continue;

    // If this piece is zero, it wipes out the chunk entirely, and we can
    // drop it.
    if (maskPiece == 0) {
      pv = payloadTy;
      continue;
    }
    
    // Otherwise, apply the mask to the existing value.
    auto v = pv.get<llvm::Value*>();
    auto payloadIntTy = llvm::IntegerType::get(IGF.IGM.getLLVMContext(), size);
    auto maskConstant = llvm::ConstantInt::get(payloadIntTy, maskPiece);
    v = IGF.Builder.CreateBitOrPointerCast(v, payloadIntTy);
    v = IGF.Builder.CreateAnd(v, maskConstant);
    v = IGF.Builder.CreateBitOrPointerCast(v, payloadTy);
    pv = v;
  }
}

void
EnumPayload::emitApplyOrMask(IRGenFunction &IGF, const APInt &mask) {
  // Early exit if the mask has no effect.
  if (mask == 0)
    return;

  auto maskReader = APIntReader(mask, IGF.IGM.Triple.isLittleEndian());

  auto &DL = IGF.IGM.DataLayout;
  for (auto &pv : PayloadValues) {
    auto payloadTy = getPayloadType(pv);
    unsigned size = DL.getTypeSizeInBits(payloadTy);

    // Read a chunk of the mask.
    auto maskPiece = maskReader.read(size);

    // If this piece is zero, it has no effect.
    if (maskPiece == 0)
      continue;
    
    auto payloadIntTy = llvm::IntegerType::get(IGF.IGM.getLLVMContext(), size);
    auto maskConstant = llvm::ConstantInt::get(payloadIntTy, maskPiece);
    
    // If the payload value is vacant, or the mask is all ones,
    // we can adopt the mask value directly.
    if (pv.is<llvm::Type *>() || maskPiece.isAllOnesValue()) {
      pv = IGF.Builder.CreateBitOrPointerCast(maskConstant, payloadTy);
      continue;
    }
    
    // Otherwise, apply the mask to the existing value.
    auto v = pv.get<llvm::Value*>();
    v = IGF.Builder.CreateBitOrPointerCast(v, payloadIntTy);
    v = IGF.Builder.CreateOr(v, maskConstant);
    v = IGF.Builder.CreateBitOrPointerCast(v, payloadTy);
    pv = v;
  }
}

void
EnumPayload::emitApplyOrMask(IRGenFunction &IGF,
                             EnumPayload mask) {
  unsigned count = PayloadValues.size();
  assert(count == mask.PayloadValues.size());

  auto &DL = IGF.IGM.DataLayout;
  for (unsigned i = 0; i < count; i++ ) {
    auto payloadTy = getPayloadType(PayloadValues[i]);
    unsigned size = DL.getTypeSizeInBits(payloadTy);

    auto payloadIntTy = llvm::IntegerType::get(IGF.IGM.getLLVMContext(), size);

    if (mask.PayloadValues[i].is<llvm::Type *>()) {
      // We're ORing with zero, do nothing
    } else if (PayloadValues[i].is<llvm::Type *>()) {
      PayloadValues[i] = mask.PayloadValues[i];
    } else {
      auto v1 = IGF.Builder.CreateBitOrPointerCast(
          PayloadValues[i].get<llvm::Value *>(),
          payloadIntTy);

      auto v2 = IGF.Builder.CreateBitOrPointerCast(
          mask.PayloadValues[i].get<llvm::Value *>(),
          payloadIntTy);

      PayloadValues[i] = IGF.Builder.CreateBitOrPointerCast(
          IGF.Builder.CreateOr(v1, v2),
          payloadTy);
    }
  }
}

llvm::Value *
EnumPayload::emitGatherSpareBits(IRGenFunction &IGF,
                                 const SpareBitVector &spareBits,
                                 unsigned firstBitOffset,
                                 unsigned resultBitWidth) const {
  auto &DL = IGF.IGM.DataLayout;
  llvm::Value *spareBitValue = nullptr;
  auto mask = getLowestNSetBits(spareBits.asAPInt(),
                                resultBitWidth - firstBitOffset);
  auto bitWidth = mask.countPopulation();
  auto spareBitReader = APIntReader(std::move(mask),
		                    IGF.IGM.Triple.isLittleEndian());
  auto usedBits = firstBitOffset;

  for (auto &pv : PayloadValues) {
    // If this value is zero, it has nothing to add to the spare bits.
    auto v = pv.dyn_cast<llvm::Value*>();
    if (!v) {
      spareBitReader.skip(DL.getTypeSizeInBits(pv.get<llvm::Type*>()));
      continue;
    }

    // Slice the spare bit vector.
    unsigned size = DL.getTypeSizeInBits(v->getType());
    auto spareBitsPart = spareBitReader.read(size);
    unsigned numBitsInPart = spareBitsPart.countPopulation();

    // If there were no spare bits in this part, it has nothing to add.
    if (numBitsInPart == 0)
      continue;

    if (usedBits >= bitWidth)
      break;

    unsigned offset = usedBits;
    if (!IGF.IGM.Triple.isLittleEndian()) {
      offset = bitWidth - usedBits - numBitsInPart;
    }
    // Get the spare bits from this part.
    auto bits = irgen::emitGatherBits(IGF, spareBitsPart,
                                      v, offset, bitWidth);
    usedBits += numBitsInPart;

    // Accumulate it into the full set.
    if (spareBitValue) {
      bits = IGF.Builder.CreateOr(spareBitValue, bits);
    }
    spareBitValue = bits;
  }
  auto destTy = llvm::IntegerType::get(IGF.IGM.getLLVMContext(),
                                       resultBitWidth);
  if (!spareBitValue) {
    return llvm::ConstantInt::get(destTy, 0);
  }
  if (resultBitWidth > bitWidth) {
    return IGF.Builder.CreateZExt(spareBitValue, destTy);
  }
  return spareBitValue;
}
