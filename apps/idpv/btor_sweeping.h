
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <stdlib.h>
#include "gmp.h"
#include "gmpxx.h"

#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)

struct BtorBitVector
{
  uint32_t width; /* length of bit vector */
#ifdef BTOR_USE_GMP
  mpz_t val;
#else
  uint32_t len;   /* length of 'bits' array */

  /* 'bits' represents the bit vector in 32-bit chunks, first bit of 32-bit bv
   * in bits[0] is MSB, bit vector is 'filled' from LSB, hence spare bits (if
   * any) come in front of the MSB and are zeroed out.
   * E.g., for a bit vector of width 31, representing value 1:
   *
   *    bits[0] = 0 0000....1
   *              ^ ^--- MSB
   *              |--- spare bit
   * */
  BTOR_BV_TYPE bits[];
#endif
};

struct BtorMemMgr
{
  size_t allocated;
  size_t maxallocated;
  size_t sat_allocated;
  size_t sat_maxallocated;
};

typedef struct BtorMemMgr BtorMemMgr;

typedef struct BtorBitVector BtorBitVector;

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};
#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))

uint32_t btor_bv_hash (const BtorBitVector *bv) {
    assert(bv);
    uint32_t i, j = 0, n, res = 0;
  uint32_t x, p0, p1;

  res = bv->width * hash_primes[j++];

#ifdef BTOR_USE_GMP
  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size (bv->val); i < n; ++i)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    limb = mpz_getlimbn (bv->val, i);
    if (mp_bits_per_limb == 64)
    {
      uint32_t lo = (uint32_t) limb;
      uint32_t hi = (uint32_t) (limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      p1 = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert (mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#else
  for (i = 0, j = 0, n = bv->len; i < n; i++)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    x   = bv->bits[i] ^ res;
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#endif
  return res;
}

BtorBitVector * btor_bv_new (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init (res->val);
#else
  uint32_t i;

  i = bw / BTOR_BV_TYPE_BW;
  if (bw % BTOR_BV_TYPE_BW > 0) i += 1;

  assert (i > 0);
  res =
      btor_mem_malloc (mm, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * i);
  BTOR_CLRN (res->bits, i);
  res->len = i;
  assert (res->len);
  res->width = bw;
  assert (res->width <= res->len * BTOR_BV_TYPE_BW);
#endif
  return res;
}

bool btor_util_check_bin_to_bv (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (mm);
  assert (str);
  assert (bw);

  (void) mm;
  return strlen (str) <= bw;
}


BtorBitVector *btor_bv_const(BtorMemMgr *mm, const char *str, uint32_t bw){
    assert (btor_util_check_bin_to_bv (mm, str, bw));

    BtorBitVector *res;

#ifdef BTOR_USE_GMP
    BTOR_NEW (mm, res);
    res->width = bw;
    mpz_init_set_str (res->val, str, 2);
#else
    uint32_t i, j, bit;
    res = btor_bv_new (mm, bw);
    for (i = 0; i < bw; i++)
    {
        j = bw - 1 - i;
        assert (str[j] == '0' || str[j] == '1');
        bit = str[j] == '0' ? 0 : 1;
        btor_bv_set_bit (res, i, bit);
    }
#endif
    return res;
}

//trasform a bv to btorbv
// Btor *btor = boolector_new();
const char *assignment = boolector_bv_assignment(btor, term.node);