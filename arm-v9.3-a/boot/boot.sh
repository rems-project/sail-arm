#!/usr/bin/env bash
set -e

BOOT_DIR=$(realpath $(dirname "$0"))

if [ -z `command -v dtc` ]
then
    echo "device tree compiler (dtc) not found"
    echo "on ubuntu, apt install device-tree-compiler"
fi

if [ ! -f ${EMULATOR:=c/armv9} ]
then
    echo "cannot find C emulator;  make sure it is built by running \`make gen_c\`, and set the EMULATOR environment variable if it is at a path other than ${EMULATOR}"
    exit 1
fi

BOOT="https://github.com/Alasdair/sail-arm-boot/archive/master.zip"

while true; do
    read -p "Download boot files from $BOOT (y/n)? " yn
    case $yn in
	[Yy]* )
	    curl -L $BOOT 1> boot.zip;
	    break;;
	[Nn]* ) break;;
	* ) echo "Please answer yes or no.";;
    esac
done

if [ ! -f boot.zip ]
then
    echo "existing boot.zip could not be found, exiting"
    exit 1
fi

unzip -u boot.zip
mkdir -p sail-arm-boot-master/initramfs

echo "Building bootloader"
make -C sail-arm-boot-master bootloader.bin

echo "Building initramfs"
make -C sail-arm-boot-master initramfs

echo "Building device tree blob"
make -C sail-arm-boot-master sail.dtb

LINUX="https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.0.7.tar.xz"

while true; do
    read -p "Download Linux from $LINUX (y/n)? " yn
    case $yn in
	[Yy]* )
	    wget $LINUX;
	    break;;
	[Nn]* ) break;;
	* ) echo "Please answer yes or no.";;
    esac
done

if [ ! -f linux-6.0.7.tar.xz ]
then
    echo "existing linux-6.0.7 could not be found, exiting"
    exit 1
fi

echo "Unpacking Linux"
tar -xf linux-6.0.7.tar.xz

echo "Copying config file"
cp ${BOOT_DIR}/config-linux-6.0.7 linux-6.0.7/.config

echo "Building Linux"
make -C linux-6.0.7 ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- -k -j 8

cp linux-6.0.7/arch/arm64/boot/Image .
cp sail-arm-boot-master/bootloader.bin .
cp sail-arm-boot-master/sail.dtb .

echo "Starting emulator"
${EMULATOR} -b 0x80000000,bootloader.bin -b 0x81000000,sail.dtb -b 0x82080000,Image -C cpu.cpu0.RVBAR=0x80000000 -C cpu.has_tlb=0x0 2> /dev/null || true

rm -f bootloader.bin
rm -f sail.dtb
rm -f Image

exit 0
