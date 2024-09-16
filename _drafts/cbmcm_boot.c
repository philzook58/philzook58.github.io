#ifndef MASK_ROM_H
2 #define MASK_ROM_H 3 4 #include < string.h > 5 #include < stdint.h >
    6 #include < malloc.h > 7 #include < stdlib.h > 8 #include < memory.h >
    9 10 #define __REACHABILITY_CHECK __CPROVER_assert(
        0, "Reachability check , should always → \033[0;31mFAIL\033[0m");
11 #define MAX_ROM_EXTS 1 12 #define RSA_SIZE 96 13 #define PMP_REGIONS 16 14 #define MAX_IMAGE_LENGTH 2 // necessary constraint in order to terminate CBMC verification
    15 16 17 // Represents a signature. Needed for CBMC OBJECT_SIZE to see if
             // signature is of ok size
    18 typedef struct signature_t {
  19 int32_t value[RSA_SIZE];
  20 // something else
      21
} signature_t;
22 23 24 // Represents a public key
    25 typedef struct pub_key_t {
  26 int32_t exponent;
  27 int32_t modulus[RSA_SIZE];
  28 // something else
      29
} pub_key_t;
30 31 32 // Struct representing rom_ext_manifest
    33 typedef struct rom_ext_manifest_t {
  34 uint32_t identifier;
  35 36 signature_t signature;
  37 38 // public part of signature key
      39 pub_key_t pub_signature_key;
  40 uint32_t image_length;
  41 char *image_code;
  42
} rom_ext_manifest_t;

44 45 // Returned by rom_ext_manifests_to_try
    46 typedef struct rom_exts_manifests_t {
  47 int size;
  48 rom_ext_manifest_t rom_exts_mfs[MAX_ROM_EXTS];
  49
} rom_exts_manifests_t;
50 51 52 // Represents boot policy
    53 typedef struct boot_policy_t {
  54 int identifier;
  55 56 // which rom_ext_slot to boot
      57 int rom_ext_slot;
  58 59 // what to do if all ROM Ext are invalid
      60 char *fail;
  61 62 // what to do if the ROM Ext unexpectedly returns
      63 char *fail_rom_ext_terminated;
  64 65
} boot_policy_t;
66 67 68 69 // Represents a pmp region
    70 typedef struct __PMP_region_t {
  71 int identifier;
  72 73 // Locked , Read , Write , Execute
      74 int R;
  75 int W;
  76 int E;
  77 int L;
  78 79
} __PMP_region_t;
80 81 82 typedef struct __PMP_regions_t {
  83 // There are 16 PMP regions (0...15)
      84 __PMP_region_t pmp_regions[PMP_REGIONS];
  85
} __PMP_regions_t;
86 87 #endif