
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <stdlib.h>
#include <gmp.h>
#include "gmpxx.h"

//----------------CONFIG--------------
//------------------------------------
// #define BTOR_USE_GMP 1



#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)
static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};
#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))

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

#define BTOR_NEWN(ptr)                                          \
  do                                                                        \
  {                                                                         \
    (ptr) = (decltype(ptr)) malloc(1 * sizeof *(ptr)); \
  } while (0)

#define BTOR_CNEWN(ptr, nelems)                                        \
  do                                                                       \
  {                                                                        \
    (ptr) = (decltype(ptr)) calloc((nelems), sizeof *(ptr)); \
  } while (0)

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

#define BTOR_NEW(ptr) BTOR_NEWN (ptr)

void *
btor_mem_malloc (size_t size)
{
  void *result;
  if (!size) return 0;
  result = malloc (size);
  return result;
}


BtorBitVector *btor_bv_new (uint32_t bw)
{
  assert (bw > 0);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init (res->val);
#else
  uint32_t i;
  i = bw / BTOR_BV_TYPE_BW ;
  if(bw % BTOR_BV_TYPE_BW > 0) i += 1;
  assert(i > 0);
  res = static_cast< BtorBitVector *>(malloc (sizeof (BtorBitVector) + i * sizeof (BTOR_BV_TYPE)));
  res->len = i;
  res->width = bw;
#endif
  return res;
}

uint32_t btor_bv_hash (const BtorBitVector *bv)
{
  assert (bv);

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


void btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert (bv);
  assert (bit == 0 || bit == 1);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  if (bit)
  {
    mpz_setbit (bv->val, pos);
  }
  else
  {
    mpz_clrbit (bv->val, pos);
  }
#else
  assert (bv->len > 0);
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  assert (i < bv->len);

  if (bit)
  {
    bv->bits[bv->len - 1 - i] |= (1u << j);
  }
  else
  {
    bv->bits[bv->len - 1 - i] &= ~(1u << j);
  }
#endif
}


BtorBitVector *btor_bv_const (const char *str, uint32_t bw)
{
  assert ( strlen (str) <= bw);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init_set_str (res->val, str, 2);
#else
  uint32_t i, j, bit;
  res = btor_bv_new (bw);
  for (i = 0; i < bw; i++)
  {
    j = bw - 1 - i;
    // assert (str[j] == '0' || str[j] == '1');
    bit = str[j] == '0' ? 0 : 1;
    btor_bv_set_bit (res, i, bit);
  }
#endif
  return res;
}

BtorBitVector *btor_bv_char_to_bv (const char *assignment)
{
  assert (assignment);
  assert (strlen (assignment) > 0);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = strlen (assignment);
  mpz_init_set_str (res->val, assignment, 2);
#else
  res = btor_bv_const (assignment, strlen (assignment));
#endif
  return res;
}


uint32_t btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  return mpz_tstbit (bv->val, pos);
#else
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;

  return (bv->bits[bv->len - 1 - i] >> j) & 1;
#endif
}


char *btor_bv_to_char (const BtorBitVector *bv)
{
  assert (bv);

  char *res;
  uint64_t bw = bv->width;

  BTOR_CNEWN (res, bw + 1);
#ifdef BTOR_USE_GMP
  char *tmp     = mpz_get_str (0, 2, bv->val);
  uint64_t n    = strlen (tmp);
  uint64_t diff = bw - n;
  assert (n <= bw);
  memset (res, '0', diff);
  memcpy (res + diff, tmp, n);
  assert (strlen (res) == bw);
  free (tmp);
#else
  uint64_t i;
  uint32_t bit;

  for (i = 0; i < bw; i++)
  {
    bit             = btor_bv_get_bit (bv, i);
    res[bw - 1 - i] = bit ? '1' : '0';
  }
  res[bw] = '\0';
#endif
  return res;
}


uint64_t btor_bv_to_uint64 (const BtorBitVector *bv)
{
  assert (bv);
  assert (bv->width <= sizeof (uint64_t) * 8);

  uint64_t res;

#ifdef BTOR_USE_GMP
  res = mpz_get_ui (bv->val);
#else
  assert (bv->len <= 2);
  uint32_t i;
  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));
#endif

  return res;
}

#ifndef BTOR_USE_GMP
#ifndef NDEBUG
static bool
rem_bits_zero_dbg (BtorBitVector *bv)
{
  return (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
}
#endif

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if (bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}
#endif

BtorBitVector *btor_bv_uint64_to_bv (uint64_t value, uint32_t bw)
{

  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW(res);
  res->width = bw;
  mpz_init_set_ui (res->val, value);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  res = btor_bv_new (bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_add (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_add (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  int64_t i;
  uint64_t x, y, sum;
  BTOR_BV_TYPE carry;

  if (bw <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (x + y, bw);
  }
  else
  {
    res   = btor_bv_new (bw);
    carry = 0;
    for (i = a->len - 1; i >= 0; i--)
    {
      sum          = (uint64_t) a->bits[i] + b->bits[i] + carry;
      res->bits[i] = (BTOR_BV_TYPE) sum;
      carry        = (BTOR_BV_TYPE) (sum >> 32);
    }
  }

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}


BtorBitVector *btor_bv_and (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_and (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

bool btor_bv_is_zero (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 0) == 0;
#else
  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

bool btor_bv_is_one (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 1) == 0;
#else
  uint32_t i;
  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

BtorBitVector *btor_bv_one (uint32_t bw)
{
  assert (bw);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (res);
  res->width = bw;
  mpz_init_set_ui (res->val, 1);
#else
  res = btor_bv_new (bw);
  btor_bv_set_bit (res, 0, 1);
#endif
  return res;
}

#define btor_bv_zero(BW) btor_bv_new (BW)

BtorBitVector *btor_bv_implies (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);
  assert (a->width == 1);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_zero (a) || btor_bv_is_one (b) ? btor_bv_one (1)
                                                  : btor_bv_zero (1);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~a->bits[i] | b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_or (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] | b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_nand (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_and (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] & b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *btor_bv_nor (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] | b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}