//===--- EnumImpl.h - Enum implementation runtime declarations --*- C++ -*-===//
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
//
// Enum implementation details declarations of the Swift runtime.
//
//===----------------------------------------------------------------------===//
#ifndef SWIFT_RUNTIME_ENUMIMPL_H
#define SWIFT_RUNTIME_ENUMIMPL_H

namespace swift {

static inline
void write_native_byte_order(uint8_t *dst, size_t dstLen,
                             uint32_t value, size_t valueLen,
                             bool zeroUnused = true) {
  if (valueLen > dstLen)
    swift::crash("cannot write value to dst, dst is too short");
  if (valueLen > sizeof(value))
    swift::crash("value is longer than 4 bytes");

#if defined(__LITTLE_ENDIAN__)
  // write forwards
  const std::ptrdiff_t inc = 1;
#elif defined(__BIG_ENDIAN__)
  // write backwards
  const std::ptrdiff_t inc = -1;
  dst = &dst[dstLen-1];
#else
#error "native byte order not defined"
#endif

  #pragma clang loop unroll_count(4) // fully unroll
  for (size_t i = 0; i < valueLen; ++i) {
    *dst = static_cast<uint8_t>(value >> (8*i));
    dst += inc;
  }

  if (zeroUnused) {
    #pragma clang loop unroll_count(8) // unroll to multiple of word size
    for (size_t i = 0; i < (dstLen - valueLen); ++i) {
      *dst = 0;
      dst += inc;
    }
  }
}

static inline
uint32_t read_native_byte_order(const uint8_t *src, size_t srcLen, size_t valueLen) {
  uint32_t value = 0;
  if (valueLen > srcLen)
    swift::crash("value length is larger than the src length");
  if (valueLen > sizeof(value))
    swift::crash("value length is larger than 4");

#if defined(__LITTLE_ENDIAN__)
  // read forwards
  const std::ptrdiff_t inc = 1;
#elif defined(__BIG_ENDIAN__)
  // read backwards
  const std::ptrdiff_t inc = -1;
  src = &src[srcLen-1];
#else
#error "native byte order not defined"
#endif

  #pragma clang loop unroll_count(4) // fully unroll
  for (size_t i = 0; i < valueLen; ++i) {
    value |= static_cast<uint32_t>(*src) << (i*8);
    src += inc;
  }
  return value;
}

static inline
void write_tag(uint8_t *dst, size_t dstLen, uint32_t tag, size_t tagLen) {
  if (tagLen == 0 || tagLen == 3 || tagLen > 4) {
    swift::crash("Tagbyte values should be 1, 2 or 4.");
  }
  write_native_byte_order(dst, dstLen, tag, tagLen);
}

static inline
uint32_t read_tag(const uint8_t *src, size_t srcLen, size_t tagLen) {
  if (tagLen == 0 || tagLen == 3 || tagLen > 4) {
    swift::crash("Tagbyte values should be 1, 2 or 4.");
  }
  return read_native_byte_order(src, srcLen, tagLen);
}

inline unsigned getNumTagBytes(size_t size, unsigned emptyCases,
                               unsigned payloadCases) {
  // We can use the payload area with a tag bit set somewhere outside of the
  // payload area to represent cases. See how many bytes we need to cover
  // all the empty cases.

  unsigned numTags = payloadCases;
  if (emptyCases > 0) {
    if (size >= 4)
      // Assume that one tag bit is enough if the precise calculation overflows
      // an int32.
      numTags += 1;
    else {
      unsigned bits = size * 8U;
      unsigned casesPerTagBitValue = 1U << bits;
      numTags += ((emptyCases + (casesPerTagBitValue-1U)) >> bits);
    }
  }
  return (numTags <=    1 ? 0 :
          numTags <   256 ? 1 :
          numTags < 65536 ? 2 : 4);
}

inline unsigned getEnumTagSinglePayloadImpl(
    const OpaqueValue *enumAddr, unsigned emptyCases, const Metadata *payload,
    size_t payloadSize, size_t payloadNumExtraInhabitants,
    int (*getExtraInhabitantIndex)(const OpaqueValue *, const Metadata *)) {

  // If there are extra tag bits, check them.
  if (emptyCases > payloadNumExtraInhabitants) {
    auto *valueAddr = reinterpret_cast<const uint8_t *>(enumAddr);
    auto *extraTagBitAddr = valueAddr + payloadSize;
    unsigned numBytes =
        getNumTagBytes(payloadSize, emptyCases - payloadNumExtraInhabitants,
                       1 /*payload case*/);
    unsigned extraTagBits = read_tag(extraTagBitAddr, numBytes, numBytes);

    // If the extra tag bits are zero, we have a valid payload or
    // extra inhabitant (checked below). If nonzero, form the case index from
    // the extra tag value and the value stored in the payload.
    if (extraTagBits > 0) {
      unsigned caseIndexFromExtraTagBits =
          payloadSize >= 4 ? 0 : (extraTagBits - 1U) << (payloadSize * 8U);

      // In practice we should need no more than four bytes from the payload
      // area.
      unsigned numPayloadTagBytes = std::min(size_t(4), payloadSize);
      unsigned caseIndexFromValue =
          read_native_byte_order(valueAddr, payloadSize, numPayloadTagBytes);
      unsigned noPayloadIndex =
          (caseIndexFromExtraTagBits | caseIndexFromValue) +
          payloadNumExtraInhabitants;
      return noPayloadIndex + 1;
    }
  }

  // If there are extra inhabitants, see whether the payload is valid.
  if (payloadNumExtraInhabitants > 0) {
    return getExtraInhabitantIndex(enumAddr, payload) + 1;
  }

  // Otherwise, we have always have a valid payload.
  return 0;
}

inline void storeEnumTagSinglePayloadImpl(
    OpaqueValue *value, unsigned whichCase, unsigned emptyCases,
    const Metadata *payload, size_t payloadSize,
    size_t payloadNumExtraInhabitants,
    void (*storeExtraInhabitant)(OpaqueValue *, int whichCase,
                                 const Metadata *)) {
  auto *valueAddr = reinterpret_cast<uint8_t *>(value);
  auto *extraTagBitAddr = valueAddr + payloadSize;
  unsigned numExtraTagBytes =
      emptyCases > payloadNumExtraInhabitants
          ? getNumTagBytes(payloadSize, emptyCases - payloadNumExtraInhabitants,
                           1 /*payload case*/)
          : 0;

  // For payload or extra inhabitant cases, zero-initialize the extra tag bits,
  // if any.
  if (whichCase <= payloadNumExtraInhabitants) {
    #pragma clang loop unroll_count(4) // fully unroll
    for (unsigned i = 0; i < numExtraTagBytes; ++i)
      extraTagBitAddr[i] = 0;

    // If this is the payload case, we're done.
    if (whichCase == 0)
      return;

    // Store the extra inhabitant.
    unsigned noPayloadIndex = whichCase - 1;
    storeExtraInhabitant(value, noPayloadIndex, payload);
    return;
  }

  // Factor the case index into payload and extra tag parts.
  unsigned noPayloadIndex = whichCase - 1;
  unsigned caseIndex = noPayloadIndex - payloadNumExtraInhabitants;
  unsigned payloadIndex, extraTagIndex;
  if (payloadSize >= 4) {
    extraTagIndex = 1;
    payloadIndex = caseIndex;
  } else {
    unsigned payloadBits = payloadSize * 8U;
    extraTagIndex = 1U + (caseIndex >> payloadBits);
    payloadIndex = caseIndex & ((1U << payloadBits) - 1U);
  }

  // Store into the value.
  unsigned numPayloadTagBytes = std::min(size_t(4), payloadSize);
  if (numPayloadTagBytes > 0) {
    write_native_byte_order(valueAddr, payloadSize,
                            payloadIndex, numPayloadTagBytes,
                            /* zeroUnused = */ true);
  }
  if (numExtraTagBytes > 0) {
    write_tag(extraTagBitAddr, numExtraTagBytes,
              extraTagIndex, numExtraTagBytes);
  }
}

} /* end namespace swift */

#endif /* SWIFT_RUNTIME_ENUMIMPL_H */
