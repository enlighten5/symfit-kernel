#!/bin/bash
# SYMCC_INPUT_FILE=/challenge-001-exemplar-source/test_harnesses/sample_solve.bin \
# vng -r /challenge-001-exemplar-source/arch/x86/boot/bzImage \
#     --verbose     \
#     --dry-run     \
#     --qemu /workdir/qemu/build/qemu-system-x86_64

# --accel tcg,thread=single single thread for system mode

# /workdir/qemu/build/qemu-system-x86_64 \
#     --accel tcg,thread=single -name virtme-ng -m 1G \
#     -fsdev local,id=virtfs5,path=/,security_model=none,readonly=on,multidevs=remap \
#     -device virtio-9p-pci,fsdev=virtfs5,mount_tag=/dev/root \
#     -device i6300esb,id=watchdog0 -parallel none -net none \
#     -echr 1 -chardev stdio,id=console,signal=off,mux=on \
#     -serial chardev:console -mon chardev=console -vga none -display none -smp 96 \
#     -kernel /challenge-001-exemplar-source/arch/x86/boot/bzImage \
#     -append 'virtme_hostname=virtme-ng virtme_link_mods=/challenge-001-exemplar-source/.virtme_mods/lib/modules/0.0.0 virtme_rw_overlay0=/etc virtme_rw_overlay1=/lib virtme_rw_overlay2=/home virtme_rw_overlay3=/opt virtme_rw_overlay4=/srv virtme_rw_overlay5=/usr virtme_rw_overlay6=/var earlyprintk=serial,ttyS0,115200 console=ttyS0 psmouse.proto=exps "virtme_stty_con=rows 26 cols 197 iutf8" TERM=xterm virtme_chdir=workdir/symfit-kernel/build virtme_user=root virtme_root_user=1 rootfstype=9p rootflags=version=9p2000.L,trans=virtio,access=any raid=noautodetect ro init=/usr/lib/python3/dist-packages/virtme/guest/bin/virtme-ng-init'

# add nokaslr, --accel tcg,thread=single -smp 1
# SYMCC_MEMORY_INPUT=1
/workdir/symfit-kernel/build/qemu-system-x86_64 \
    --accel tcg,thread=single -smp 1 \
    -D /workdir/sysqemu_log \
    -name virtme-ng -m 1G \
    -fsdev local,id=virtfs5,path=/,security_model=none,readonly=on,multidevs=remap \
    -device virtio-9p-pci,fsdev=virtfs5,mount_tag=/dev/root \
    -device i6300esb,id=watchdog0 -machine q35 -parallel none -net none \
    -echr 1 -chardev file,path=/proc/self/fd/2,id=dmesg \
    -device virtio-serial-pci -device virtconsole,chardev=dmesg \
    -chardev stdio,id=console,signal=off,mux=on -serial chardev:console \
    -mon chardev=console -vga none -display none \
    -kernel /workdir/symfit-kernel/run/bzImage \
    -append 'nokaslr virtme_hostname=virtme-ng nr_open=1048576 virtme_link_mods=/challenge-001-exemplar-source/.virtme_mods/lib/modules/0.0.0 virtme_rw_overlay0=/etc virtme_rw_overlay1=/lib virtme_rw_overlay2=/home virtme_rw_overlay3=/opt virtme_rw_overlay4=/srv virtme_rw_overlay5=/usr virtme_rw_overlay6=/var console=hvc0 earlyprintk=serial,ttyS0,115200 virtme_console=ttyS0 psmouse.proto=exps "virtme_stty_con=rows 20 cols 152 iutf8" TERM=xterm virtme_chdir=workdir/symfit-kernel/build virtme_user=root virtme_root_user=1 rootfstype=9p rootflags=version=9p2000.L,trans=virtio,access=any raid=noautodetect ro init=/usr/local/lib/python3.10/dist-packages/virtme/guest/bin/virtme-ng-init'

