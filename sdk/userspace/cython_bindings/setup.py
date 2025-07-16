from setuptools import setup, Extension
from Cython.Build import cythonize
import os

fpga_mgmt_extension = Extension(
    name="fpga_mgmt_wrapper",
    sources=["fpga_mgmt_wrapper.pyx"],
    libraries=["fpga_mgmt"],
    library_dirs=[
        os.path.join(os.environ["SDK_DIR"], "userspace/lib/so"),
        os.path.join(os.environ["SDK_DIR"], "userspace/lib"),
    ],
    include_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/include")],
    extra_compile_args=["-Wno-address-of-packed-member"],
)

fpga_pci_extension = Extension(
    name="fpga_pci_wrapper",
    sources=["fpga_pci_wrapper.pyx"],
    libraries=["fpga_mgmt"],
    library_dirs=[
        os.path.join(os.environ["SDK_DIR"], "userspace/lib/so"),
        os.path.join(os.environ["SDK_DIR"], "userspace/lib"),
    ],
    extra_objects=[os.path.join(os.environ["SDK_DIR"], "userspace/lib/libfpga_pci.a")],
    include_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/include")],
    extra_compile_args=["-Wno-address-of-packed-member"],
)

fpga_clkgen_extension = Extension(
    name="fpga_clkgen_wrapper",
    sources=["fpga_clkgen_wrapper.pyx"],
    libraries=["fpga_mgmt"],
    library_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/lib/so")],
    extra_objects=[
        os.path.join(os.environ["SDK_DIR"], "userspace/lib/libfpga_clkgen.a")
    ],
    include_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/include")],
    extra_compile_args=["-Wno-address-of-packed-member"],
)

fpga_utils_extension = Extension(
    name="fpga_utils",
    sources=["fpga_utils.pyx"],
    libraries=["fpga_mgmt"],
    library_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/lib/so")],
    include_dirs=[os.path.join(os.environ["SDK_DIR"], "userspace/include")],
    extra_compile_args=["-Wno-address-of-packed-member"],
)


setup(
    name="fpga_wrappers",
    ext_modules=cythonize(
        [
            fpga_utils_extension,
            fpga_mgmt_extension,
            fpga_pci_extension,
            fpga_clkgen_extension,
        ],
        language_level=3,
    ),
)
