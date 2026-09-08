#!/usr/bin/env python3
import os
# Adds two new on-silicon demo modes to the gr3ftl firmware, mirroring
# ATTACK_MEGIS exactly:
#   ATTACK_DFTL  (14): DFTL-style demand-paged mapping. A read of the attacker
#                      LSA misses the cached mapping table (CMT) and demand-pages
#                      in an entry that (maliciously) resolves to the victim's
#                      physical slice -- an aliasing remap.  The checked build
#                      enforces Inv2 injectivity on the paged-in entry via the
#                      reverse map and refuses the alias.
#   ATTACK_DEDUP (15): content dedup across tenants.  Tenant B's read is served
#                      from tenant A's shared physical slice (dedup).  The checked
#                      build refuses the cross-namespace share (Inv7 namespace
#                      isolation) using the reverse map + per-LSA namespace.
# Both hooks are READ-path only (like MegIS's read fast-path); no write-path or
# GC changes.  Idempotent: re-running is a no-op.

S = os.environ.get("GR3FTL_SRC",
        "/path/to/openssd/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2/ftl/run-gr3ftl/src")

def rd(p): return open(f"{S}/{p}").read()
def wr(p, s): open(f"{S}/{p}", "w").write(s); print(f"{p}: written")

# ---------------- ftl_config.h ----------------
p = "ftl_config.h"; s = rd(p)
if "ATTACK_DFTL" not in s:
    s = s.replace("#define ATTACK_MEGIS\t13",
                  "#define ATTACK_MEGIS\t13\n"
                  "#define ATTACK_DFTL\t14\n"
                  "#define ATTACK_DEDUP\t15", 1)
    s = s.replace("#define MEGIS_REGISTER_LSA\t4095",
                  "#define MEGIS_REGISTER_LSA\t4095\n"
                  "#define DFTL_VICTIM_LSA\t\t3072\n"
                  "#define DFTL_ATTACKER_LSA\t3088\n"
                  "#define DEDUP_TENANTA_LSA\t5120\n"
                  "#define DEDUP_TENANTB_LSA\t6144\n"
                  "#define DEDUP_NS_SPLIT\t\t6000\n"
                  "#define DedupNsOfLsa(lsa)\t(((lsa) >= DEDUP_NS_SPLIT) ? 2u : 1u)", 1)
    wr(p, s)
else:
    print("config: already has ATTACK_DFTL/ATTACK_DEDUP")

# ---------------- address_translation.c ----------------
p = "address_translation.c"; s = rd(p)
if "DftlDemandPageIn" in s:
    print("address_translation.c: already patched");
else:
    # (1) DFTL demand-paging helper + CMT, inserted before AddrTransRead
    helper = (
"#if (ATTACK_MODE == ATTACK_DFTL)\n"
"/* DFTL demand-paged mapping demo: the L2P is not fully resident.  A read of an\n"
"   LSA whose entry is not in the cached mapping table (CMT) triggers a demand\n"
"   page-in of that entry from the translation-page store.  The malicious page-in\n"
"   resolves the attacker LSA to the VICTIM's physical slice (an aliasing remap).\n"
"   The checked build enforces Inv2 injectivity on the paged-in entry using the\n"
"   reverse map and refuses the alias; the attack build installs it. */\n"
"static unsigned int dftlCmtVsa = VSA_NONE;\n"
"static unsigned int dftlCmtResident = 0;\n"
"\n"
"static unsigned int DftlDemandPageIn(unsigned int logicalSliceAddr)\n"
"{\n"
"\tunsigned int victimVirtualSliceAddr;\n"
"\n"
"\tif(dftlCmtResident)\n"
"\t\treturn dftlCmtVsa;\n"
"\n"
"\t(void)logicalSliceAddr;\n"
"\tvictimVirtualSliceAddr =\n"
"\t\tlogicalSliceMapPtr->logicalSlice[DFTL_VICTIM_LSA].virtualSliceAddr;\n"
"\tif(victimVirtualSliceAddr == VSA_NONE)\n"
"\t\treturn VSA_NONE;\n"
"#if CERTIFLASH_GUARD\n"
"\tif(virtualSliceMapPtr->virtualSlice[victimVirtualSliceAddr].logicalSliceAddr != DFTL_ATTACKER_LSA)\n"
"\t{\n"
"\t\txil_printf(\"[CERTIFLASH] DFTL DENY demand-paged remap LSA %d -> VSA %d: Inv2 injectivity (owner %d)\\r\\n\",\n"
"\t\t\tDFTL_ATTACKER_LSA, victimVirtualSliceAddr,\n"
"\t\t\tvirtualSliceMapPtr->virtualSlice[victimVirtualSliceAddr].logicalSliceAddr);\n"
"\t\treturn VSA_NONE;\n"
"\t}\n"
"#endif\n"
"\tdftlCmtVsa = victimVirtualSliceAddr;\n"
"\tdftlCmtResident = 1;\n"
"\txil_printf(\"[ATTACK_DFTL] demand page-in LSA %d -> victim VSA %d (alias installed)\\r\\n\",\n"
"\t\tDFTL_ATTACKER_LSA, victimVirtualSliceAddr);\n"
"\treturn victimVirtualSliceAddr;\n"
"}\n"
"#endif\n\n")
    anchor_sig = "unsigned int AddrTransRead(unsigned int logicalSliceAddr)\n"
    assert s.count(anchor_sig) == 1, "AddrTransRead signature anchor"
    s = s.replace(anchor_sig, helper + anchor_sig, 1)

    # (2) DFTL + DEDUP read-path hooks, inserted right after the MegIS read block
    megis_read_end = ("\t\t\treturn megisCoarseVsa[logicalSliceAddr - MEGIS_BASE_LSA];\n"
                      "#endif\n")
    assert s.count(megis_read_end) == 1, "MegIS read-block end anchor"
    hooks = (
"#if (ATTACK_MODE == ATTACK_DFTL)\n"
"\t\tif(logicalSliceAddr == DFTL_ATTACKER_LSA)\n"
"\t\t{\n"
"\t\t\tunsigned int pagedVirtualSliceAddr = DftlDemandPageIn(logicalSliceAddr);\n"
"\t\t\tif(pagedVirtualSliceAddr != VSA_NONE)\n"
"\t\t\t\treturn pagedVirtualSliceAddr;\n"
"\t\t}\n"
"#endif\n"
"#if (ATTACK_MODE == ATTACK_DEDUP)\n"
"\t\tif(logicalSliceAddr == DEDUP_TENANTB_LSA)\n"
"\t\t{\n"
"\t\t\tunsigned int donorVirtualSliceAddr =\n"
"\t\t\t\tlogicalSliceMapPtr->logicalSlice[DEDUP_TENANTA_LSA].virtualSliceAddr;\n"
"\t\t\tif(donorVirtualSliceAddr != VSA_NONE)\n"
"\t\t\t{\n"
"\t\t\t\tunsigned int donorOwnerLsa =\n"
"\t\t\t\t\tvirtualSliceMapPtr->virtualSlice[donorVirtualSliceAddr].logicalSliceAddr;\n"
"#if CERTIFLASH_GUARD\n"
"\t\t\t\tif(DedupNsOfLsa(donorOwnerLsa) != DedupNsOfLsa(logicalSliceAddr))\n"
"\t\t\t\t\txil_printf(\"[CERTIFLASH] DEDUP DENY cross-namespace share LSA %d (ns %d) <- LSA %d (ns %d): Inv7 namespace isolation\\r\\n\",\n"
"\t\t\t\t\t\tDEDUP_TENANTB_LSA, DedupNsOfLsa(logicalSliceAddr),\n"
"\t\t\t\t\t\tdonorOwnerLsa, DedupNsOfLsa(donorOwnerLsa));\n"
"\t\t\t\telse\n"
"#endif\n"
"\t\t\t\t{\n"
"\t\t\t\t\txil_printf(\"[ATTACK_DEDUP] read LSA %d served from donor LSA %d VSA %d (cross-tenant share)\\r\\n\",\n"
"\t\t\t\t\t\tDEDUP_TENANTB_LSA, donorOwnerLsa, donorVirtualSliceAddr);\n"
"\t\t\t\t\treturn donorVirtualSliceAddr;\n"
"\t\t\t\t}\n"
"\t\t\t}\n"
"\t\t}\n"
"#endif\n")
    s = s.replace(megis_read_end, megis_read_end + hooks, 1)
    wr(p, s)
    print("address_translation.c: DFTL + DEDUP read hooks applied")

print("DONE")
