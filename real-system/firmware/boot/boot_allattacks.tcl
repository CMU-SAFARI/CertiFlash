proc step {msg} { puts "=== $msg ==="; flush stdout }
proc retry_dow {elfPath tag} {
	for {set i 1} {$i <= 3} {incr i} {
		puts "=== download $tag attempt $i/3 ==="
		flush stdout
		if {[catch {dow $elfPath} err]} {
			puts "=== download $tag failed: $err ==="
			catch {stop}
			catch {rst -processor -clear-registers}
			after 2000
		} else {
			return 0
		}
	}
	return 1
}

# Local paths -- edit for your OpenSSD/DaisyPlus build tree:
set WS  "/path/to/openssd/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2"
set OUT "/path/to/build"

connect
step "targets"
targets
step "select PS TAP"
catch {targets -set -filter {name =~ "PS TAP*"}}
catch {rst -system}
after 3000
step "select PL"
targets -set -filter {name =~ "PL"}
step "program bitstream"
fpga -file $WS/ftl/_ide/bitstream/sys_top_wrapper.bit
step "select PSU"
targets -set -filter {name =~ "PSU"}
source $WS/ftl/_ide/psinit/psu_init.tcl
step "run psu_init"
psu_init
step "remove isolation"
psu_ps_pl_isolation_removal
step "pl reset config"
psu_ps_pl_reset_config
step "select A53"
targets -set -filter {name =~ "Cortex-A53 #0*"}
catch {stop}
catch {rst -processor}
after 1000
step "download fsbl"
if {[retry_dow $WS/daisyplus_new/export/daisyplus_new/sw/boot/fsbl.elf fsbl]} {
	error "FSBL download failed after retries"
}
step "run fsbl"
con
after 12000
catch {stop}
after 1000
catch {rst -processor -clear-registers}
after 1500
step "download ftl"
if {[retry_dow $OUT/ftl_allattacks_headless.elf ftl]} {
	error "FTL download failed after retries"
}
step "run headless FTL (no halt, no inject) - leave running"
con
after 8000
step "done - firmware running headless, core never halted"
disconnect
