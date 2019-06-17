//===--- APInt.h - Utilities for building and splitting APInts -----------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2019 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#pragma once

#include "swift/Basic/ClusteredBitVector.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SmallVector.h"

namespace swift {
namespace irgen {

class APIntBuilder {
  using APInt = llvm::APInt;

  llvm::SmallVector<APInt, 8> Elements;
  bool LittleEndian;
public:
  APIntBuilder(bool littleEndian) : LittleEndian(littleEndian) {}

  void append(const APInt &value) {
    Elements.push_back(value);
  }

  void append(APInt &&value) {
    Elements.push_back(std::move(value));
  }

  void append(const ClusteredBitVector &value) {
    if (!value.empty()) {
      Elements.push_back(value.asAPInt());
    }
  }

  void appendOnes(unsigned numBits) {
    if (numBits) {
      Elements.push_back(APInt::getAllOnesValue(numBits));
    }
  }

  void appendZeros(unsigned numBits) {
    if (numBits) {
      Elements.push_back(APInt::getNullValue(numBits));
    }
  }

  llvm::Optional<APInt> build() {
    if (Elements.size() == 0) {
      return llvm::Optional<APInt>();
    }
    unsigned size = 0;
    for (const auto &e : Elements) {
      size += e.getBitWidth();
    }
    auto result = APInt::getNullValue(size);
    unsigned offset = 0;
    for (const auto &e : Elements) {
      unsigned index = offset;
      if (!LittleEndian) {
        index = size - offset - e.getBitWidth();
      }
      result.insertBits(e, index);
      offset += e.getBitWidth();
    }
    return result;
  }

  ClusteredBitVector buildBitVector() {
    if (auto result = build()) {
      return ClusteredBitVector::fromAPInt(std::move(result.getValue()));
    }
    return {};
  }
};

/// APIntReader allows an APInt to be read from in chunks. Chunks may
/// be read starting from either the least significant bit
/// (little-endian) or the most significant bit (big-endian).
///
/// This is useful when interpreting an APInt as a multi-byte mask
/// that needs to be applied to a composite value in memory.
///
/// Example:
///
///   // big-endian
///   auto x = APIntReader(APInt(32, 0x1234), false);
///   x.read(16) // 0x12
///   x.read(8)  // 0x3
///   x.read(8)  // 0x4
///
///   // little-endian
///   auto y = APIntReader(APInt(32, 0x1234), true);
///   y.read(16) // 0x34
///   y.read(8)  // 0x2
///   y.read(8)  // 0x1
///
class APIntReader {
  using APInt = llvm::APInt;

  const APInt Value;
  const bool LittleEndian;
  unsigned Offset;
public:
  /// If the reader is in little-endian mode then bits will be read
  /// from the least significant to the most significant. Otherwise
  /// they will be read from the most significant to the least
  /// significant.
  APIntReader(const APInt &value, bool littleEndian) :
      Value(value),
      LittleEndian(littleEndian),
      Offset(0) {}

  /// Read the given number of bits from the unread part of the
  /// underlying value and adjust the remaining value as appropriate.
  APInt read(unsigned numBits) {
    assert(Value.getBitWidth() >= Offset + numBits);
    unsigned offset = Offset;
    if (!LittleEndian) {
      offset = Value.getBitWidth() - offset - numBits;
    }
    Offset += numBits;
    return Value.extractBits(numBits, offset);
  }

  // Skip the number of bits provided.
  void skip(unsigned numBits) {
    assert(Value.getBitWidth() >= Offset + numBits);
    Offset += numBits;
  }
};

} // end namespace irgen
} // end namespace swift

