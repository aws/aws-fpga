#!/usr/bin/env groovy

//=============================================================================
// Pipeline parameters
//=============================================================================
properties([parameters([
    string(name: 'branch', defaultValue: ''),
    booleanParam(name: 'test_markdown_links',                 defaultValue: true,  description: 'Test markdown files and check for broken links'),
    booleanParam(name: 'test_src_headers',                    defaultValue: true,  description: 'Check copyright heaers of source files'),
    booleanParam(name: 'test_fpga_tools',                     defaultValue: true,  description: 'Test fpga-* commands on F1'),
    booleanParam(name: 'test_hdk_scripts',                    defaultValue: true,  description: 'Test the HDK setup scripts'),
    booleanParam(name: 'test_sims',                           defaultValue: true,  description: 'Run all Simulations'),
    booleanParam(name: 'test_edma',                           defaultValue: true,  description: 'Run EDMA unit and perf tests'),
    booleanParam(name: 'test_non_root_access',                defaultValue: true,  description: 'Test non-root access to FPGA tools'),
    booleanParam(name: 'test_xdma',                           defaultValue: true,  description: 'Test XDMA driver'),
    booleanParam(name: 'test_runtime_software',               defaultValue: true,  description: 'Test precompiled AFIs'),
    booleanParam(name: 'test_dcp_recipes',                    defaultValue: false, description: 'Run DCP generation with all clock recipes and build strategies.'),
    booleanParam(name: 'test_hdk_fdf',                        defaultValue: true,  description: 'Run Full developer flow testing on cl_hello_world and cl_dram_dma'),
    booleanParam(name: 'test_sdaccel_scripts',                defaultValue: true,  description: 'Test SDAccel setup scripts'),
    booleanParam(name: 'test_all_sdaccel_examples_fdf',       defaultValue: false, description: 'Run Full Developer Flow testing of all SDAccel examples. This overrides test_helloworld_sdaccel_example'),
    booleanParam(name: 'test_helloworld_sdaccel_example_fdf', defaultValue: true,  description: 'Run Full Developer Flow testing of the Hello World SDAccel example'),
    booleanParam(name: 'debug_dcp_gen',                       defaultValue: false, description: 'Only run FDF on cl_hello_world. Overrides test_*.'),
    booleanParam(name: 'debug_fdf_uram',                      defaultValue: false, description: 'Debug the FDF for cl_uram_example.'),
    booleanParam(name: 'fdf_ddr_comb',                        defaultValue: false, description: 'run FDF for cl_dram_dma ddr combinations.'),
    booleanParam(name: 'disable_runtime_tests',               defaultValue: false,  description: 'Option to disable runtime tests.'),
    booleanParam(name: 'use_test_ami',                        defaultValue: false,  description: 'This option asks for the test AMI from Jenkins'),
    booleanParam(name: 'internal_simulations',                defaultValue: false, description: 'This option asks for default agent from Jenkins')
])])

//=============================================================================
// Configuration
//=============================================================================
boolean test_markdown_links = params.get('test_markdown_links')
boolean test_src_headers = params.get('test_src_headers')
boolean test_hdk_scripts = params.get('test_hdk_scripts')
boolean test_fpga_tools = params.get('test_fpga_tools')
boolean test_sims = params.get('test_sims')
boolean test_edma = params.get('test_edma')
boolean test_non_root_access = params.get('test_non_root_access')
boolean test_xdma = params.get('test_xdma')
boolean test_runtime_software = params.get('test_runtime_software')
boolean test_dcp_recipes = params.get('test_dcp_recipes')
boolean test_hdk_fdf = params.get('test_hdk_fdf')
boolean test_sdaccel_scripts = params.get('test_sdaccel_scripts')
boolean test_all_sdaccel_examples_fdf = params.get('test_all_sdaccel_examples_fdf')
boolean test_helloworld_sdaccel_example_fdf = params.get('test_helloworld_sdaccel_example_fdf')
boolean disable_runtime_tests = params.get('disable_runtime_tests')

def runtime_sw_cl_names = ['cl_dram_dma', 'cl_hello_world']
def dcp_recipe_cl_names = ['cl_dram_dma', 'cl_hello_world']
def dcp_recipe_scenarios = [
    // Default values are tested in FDF: A0-B0-C0-DEFAULT
    // Fastest clock speeds are: A1-B2-C0
    // Test each clock recipe with the BASIC strategy
    // Test all strategies with highest clock speeds
    'A1-B1-C1-BASIC',
    'A1-B2-C0-BASIC',
    'A2-B3-C2-BASIC',
    'A1-B4-C3-BASIC',
    'A1-B5-C0-BASIC',
    'A1-B2-C0-DEFAULT',
    'A1-B2-C0-EXPLORE',
    'A1-B2-C0-TIMING',
    'A1-B2-C0-TIMING',
    'A1-B2-C0-CONGESTION',
    ]
def fdf_test_names = ['cl_dram_dma[A1-B0-C0-DEFAULT]', 'cl_hello_world[A0-B0-C0-DEFAULT]', 'cl_hello_world_vhdl',
    'cl_uram_example[2]', 'cl_uram_example[3]', 'cl_uram_example[4]']

boolean debug_dcp_gen = params.get('debug_dcp_gen')
if (debug_dcp_gen) {
    fdf_test_names = ['cl_hello_world[A0-B0-C0-DEFAULT]']
    test_markdown_links = false
    test_sims = false
    test_runtime_software = false
    test_sdaccel_scripts = false
}

boolean debug_fdf_uram = params.get('debug_fdf_uram')
if (debug_fdf_uram) {
    fdf_test_names = ['cl_uram_example[2]', 'cl_uram_example[3]', 'cl_uram_example[4]']
    test_markdown_links = false
    test_sims = false
    test_runtime_software = false
    test_sdaccel_scripts = false
}

boolean fdf_ddr_comb = params.get('fdf_ddr_comb')
if(fdf_ddr_comb) {
   fdf_test_names = ['cl_dram_dma[A0-B0-C0-DEFAULT-111]', 'cl_dram_dma[A0-B0-C0-DEFAULT-110]', 'cl_dram_dma[A0-B0-C0-DEFAULT-101]','cl_dram_dma[A0-B0-C0-DEFAULT-100]','cl_dram_dma[A0-B0-C0-DEFAULT-011]','cl_dram_dma[A0-B0-C0-DEFAULT-010]','cl_dram_dma[A0-B0-C0-DEFAULT-001]','cl_dram_dma[A0-B0-C0-DEFAULT-000]']
    test_markdown_links = false
    test_sims = false
    test_runtime_software = false
    test_sdaccel_scripts = false
}

//=============================================================================
// Globals
//=============================================================================

// Map that contains stages of tests
def all_tests = [:]

// Task to Label map
task_label = [
    'create_afi':        't2.l_50',
    'simulation':        'z1d.l',
    'dcp_gen':           'z1d.2xl',
    'runtime':           'f1.2xl',
    'runtime_all_slots': 'f1.16xl',
    'source_scripts':    'c4.xl',
    'md_links':          'c4.xl',
    'find_tests':        't2.l_50',
    'sdaccel_builds':    'z1d.2xl'
]

def xilinx_versions = [ '2017.4', '2018.2' ]
def default_xilinx_version = xilinx_versions.last()

def dsa_map = [ '2017.4' : [ 'DYNAMIC_5_0' : 'dyn'],
                '2018.2' : [ 'DYNAMIC_5_0' : 'dyn']
]

def sdaccel_example_default_map = [ '2017.4' : [ 'Hello_World_1ddr': 'SDAccel/examples/xilinx/getting_started/host/helloworld_ocl',
                                                 'Gmem_2Banks_2ddr': 'SDAccel/examples/xilinx/getting_started/kernel_to_gmem/gmem_2banks_ocl',
                                                 'kernel_3ddr_bandwidth_4ddr': 'SDAccel/examples/aws/kernel_3ddr_bandwidth',
                                                 'Kernel_Global_Bw_4ddr': 'SDAccel/examples/xilinx/getting_started/kernel_to_gmem/kernel_global_bandwidth',
                                                 'RTL_Vadd_Debug': 'SDAccel/examples/xilinx/getting_started/rtl_kernel/rtl_vadd_hw_debug'
                                               ],
                                    '2018.2' : [ 'Hello_World_1ddr': 'SDAccel/examples/xilinx/getting_started/host/helloworld_ocl',
                                                 'Gmem_2Banks_2ddr': 'SDAccel/examples/xilinx/getting_started/kernel_to_gmem/gmem_2banks_ocl',
                                                 'kernel_3ddr_bandwidth_4ddr': 'SDAccel/examples/aws/kernel_3ddr_bandwidth',
                                                 'Kernel_Global_Bw_4ddr': 'SDAccel/examples/xilinx/getting_started/kernel_to_gmem/kernel_global_bandwidth',
                                                 'RTL_Vadd_Debug': 'SDAccel/examples/xilinx/getting_started/rtl_kernel/rtl_vadd_hw_debug'
                                               ]
]

def simulator_tool_default_map = [ '2017.4' : [ 'vivado': 'xilinx/SDx/2017.4_04112018',
                                                'vcs': 'vcs-mx/L-2016.06-1',
                                                'questa': 'questa/10.6b',
                                                'ies': 'incisive/15.20.063'
                                              ],
                                   '2018.2' : [ 'vivado': 'xilinx/SDx/2018.2_06142018',
                                                'vcs': 'vcs-mx/N-2017.12-SP1-1',
                                                'questa': 'questa/10.6c_1',
                                                'ies': 'incisive/15.20.063'
                                              ]
]


// Get serializable entry set
@NonCPS def entrySet(m) {m.collect {k, v -> [key: k, value: v]}}

@NonCPS
def is_public_repo() {
    echo "Change URL: ${env.CHANGE_URL}"
    return (env.CHANGE_URL =~ /^(\S+)?aws-fpga\/pull\/(\d+)$/)
}

def get_task_label(Map args=[ : ]) {
    String task_label = args.xilinx_version + '_' + task_label[args.task]
    //boolean use_test_ami = params.get('use_test_ami')

    if (params.use_test_ami) {
        echo "Test AMI Requested"
        task_label = task_label + '_test'
    }
    if (params.internal_simulations) {
        echo "internal simulation agent requested"
        task_label = 'f1'
    }

    echo "Label Requested: $task_label"
    return task_label
}

def abort_previous_running_builds() {
    def hi = Hudson.instance
    def pname = env.JOB_NAME.split('/')[0]

    hi.getItem(pname).getItem(env.JOB_BASE_NAME).getBuilds().each{ build ->
    def executor = build.getExecutor()

    if (build.number != currentBuild.number && build.number < currentBuild.number && executor != null) {
        executor.interrupt(
            Result.ABORTED,
            new CauseOfInterruption.UserInterruption(
            "Aborted by #${currentBuild.number}"))
        println("Aborted previous running build #${build.number}")
    }
    else {
      println("Build is not running or is current build, not aborting - #${build.number}")
    }
  }
}

// Wait for input if we are running on a public repo to avoid malicious PRS
if (is_public_repo()) {
    input "Running on a public repository, do you want to proceed with running the tests?"
}
else {
    echo "Running on a private repository"
}


//Abort previous builds on PR when we push new commits
// env.CHANGE_ID is only available on PR's and not on branch builds
if (env.CHANGE_ID) {
    abort_previous_running_builds()
}

//=============================================================================
// Shared Tests
//=============================================================================


if (test_markdown_links || test_src_headers) {
    all_tests['Documentation Tests'] = {
        node(get_task_label(task: 'md_links', xilinx_version: default_xilinx_version)) {
            checkout scm
            commitChangeset = sh(returnStdout: true, script: 'git diff-tree --no-commit-id --name-status -r HEAD').trim()
            echo "${commitChangeset}"

            if (test_markdown_links) {
                stage('Test Markdown Links') {
                    String report_file = 'test_md_links.xml'
                    try {
                        sh """
                            set -e
                            source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                            python2.7 -m pytest -v $WORKSPACE/shared/tests/test_md_links.py --junit-xml $WORKSPACE/${report_file}
                        """
                    } finally {
                        if (fileExists(report_file)) {
                            junit healthScaleFactor: 10.0, testResults: report_file
                        }
                        else {
                            echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                        }
                    }
                }
            }
            if (test_src_headers) {
                stage('Test Source Headers') {
                    String report_file = 'test_check_src_headers.xml'
                    checkout scm
                    try {
                        sh """
                            set -e
                            source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                            python2.7 -m pytest -v $WORKSPACE/shared/tests/test_check_src_headers.py --junit-xml $WORKSPACE/${report_file}
                        """
                    } finally {
                        if (fileExists(report_file)) {
                            junit healthScaleFactor: 10.0, testResults: report_file
                        }
                        else {
                            echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                        }
                    }
                }
            }
        }
    }
}

//=============================================================================
// HDK Tests
//=============================================================================

if (test_hdk_scripts) {
    all_tests['Test HDK Scripts'] = {
        stage('Test HDK Scripts') {
            String report_file = 'test_hdk_scripts.xml'
            node(get_task_label(task: 'source_scripts', xilinx_version: default_xilinx_version)) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        python2.7 -m pytest -v $WORKSPACE/hdk/tests/test_hdk_scripts.py --junit-xml $WORKSPACE/${report_file}
                    """
                } finally {
                    if (fileExists(report_file)) {
                        junit healthScaleFactor: 10.0, testResults: report_file
                    }
                    else {
                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                    }
                }
            }
        }
    }
}

if (test_fpga_tools) {
    all_tests['Test FPGA Tools 1 Slot'] = {
        stage('Test FPGA Tools 1 Slot') {
            String report_file_tools = 'test_fpga_tools.xml'
            String report_file_sdk = 'test_fpga_sdk.xml'
            String report_file_combined = 'test_fpga_*.xml'
            node(get_task_label(task: 'runtime', xilinx_version: default_xilinx_version)) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        python2.7 -m pytest -v $WORKSPACE/sdk/tests/test_fpga_tools.py --junit-xml $WORKSPACE/${report_file_tools}
                        sudo -E sh -c 'source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh && python2.7 -m pytest -v $WORKSPACE/sdk/tests/test_sdk.py --junit-xml $WORKSPACE/${report_file_sdk}'
                        sudo -E chmod 666 $WORKSPACE/${report_file_sdk}
                    """
                }
                catch (exception) {
                    echo "Test FPGA Tools 1 Slot failed"
                    input message: "1 slot FPGA Tools test failed. Click Proceed or Abort when you are done debugging on the instance."
                    throw exception
                }
                finally {
                    if (fileExists(report_file_tools)) {
                        junit healthScaleFactor: 10.0, testResults: report_file_combined
                    }
                    else {
                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file_combined}"
                    }
                }
            }
        }
    }
    all_tests['Test FPGA Tools All Slots'] = {
        stage('Test FPGA Tools All Slots') {
            String report_file_tools = 'test_fpga_tools_all_slots.xml'
            String report_file_sdk = 'test_fpga_sdk_all_slots.xml'
            String report_file_combined = 'test_fpga_*_all_slots.xml'
            node(get_task_label(task: 'runtime_all_slots', xilinx_version: default_xilinx_version)) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        python2.7 -m pytest -v $WORKSPACE/sdk/tests/test_fpga_tools.py --junit-xml $WORKSPACE/${report_file_tools}
                        sudo -E sh -c 'source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh && python2.7 -m pytest -v $WORKSPACE/sdk/tests/test_sdk.py --junit-xml $WORKSPACE/${report_file_sdk}'
                        sudo -E chmod 666 $WORKSPACE/${report_file_sdk}
                    """
                }
                catch (exception) {
                    echo "Test FPGA Tools All Slots failed"
                    input message: "1 slot FPGA Tools test failed. Click Proceed or Abort when you are done debugging on the instance."
                    throw exception
                }
                finally {
                    if (fileExists(report_file_tools)) {
                        junit healthScaleFactor: 10.0, testResults: report_file_combined
                    }
                    else {
                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file_combined}"
                    }
                }
            }
        }
    }
}


if (test_sims) {
    all_tests['Run Sims'] = {
        stage('Run Sims') {
            def cl_names = ['cl_uram_example', 'cl_dram_dma', 'cl_hello_world']
            def simulators = ['vivado']
            def sim_nodes = [:]
            if(params.internal_simulations) {
              simulators = ['vcs', 'ies', 'questa', 'vivado']
            }
            for (x in cl_names) {
                for (y in xilinx_versions) {
                    for ( z in simulators)  {
                        String xilinx_version = y
                        String cl_name = x
                        String simulator = z
                        String node_name = "Sim ${cl_name} ${xilinx_version}"
                        String key = "test_${cl_name}__"
                        String report_file = "test_sims_${cl_name}_${xilinx_version}.xml"
                        def tool_module_map = simulator_tool_default_map.get(xilinx_version)
                        String vcs_module = tool_module_map.get('vcs')
                        String questa_module = tool_module_map.get('questa')
                        String ies_module = tool_module_map.get('ies')
                        String vivado_module = tool_module_map.get('vivado')
                        if(params.internal_simulations) {
                           report_file = "test_sims_${cl_name}_${xilinx_version}_${simulator}.xml"
                        }
                        sim_nodes[node_name] = {
                        node(get_task_label(task: 'simulation', xilinx_version: xilinx_version)) {
                            checkout scm
                            try {
                                if(params.internal_simulations) {
                                   sh """
                                   set -e
                                   module purge
                                   module load python/2.7.9
                                   module load ${vivado_module}
                                   module load ${vcs_module}
                                   module load ${questa_module}
                                   module load ${ies_module}
                                   source $WORKSPACE/hdk_setup.sh
                                   python2.7 -m pytest -v $WORKSPACE/hdk/tests/simulation_tests/test_sims.py -k \"${key}\" --junit-xml $WORKSPACE/${report_file} --Simulator ${simulator}
                                       """
                                } else {
                                   sh """
                                   set -e
                                   source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                   python2.7 -m pytest -v $WORKSPACE/hdk/tests/simulation_tests/test_sims.py -k \"${key}\" --junit-xml $WORKSPACE/${report_file} --Simulator ${simulator} 
                                      """
                                }
                            } catch (exc) {
                                echo "${node_name} failed: archiving results"
                                archiveArtifacts artifacts: "hdk/cl/examples/${cl_name}/verif/sim/**", fingerprint: true
                                throw exc
                            } finally {
                                if (fileExists(report_file)) {
                                    junit healthScaleFactor: 10.0, testResults: report_file
                                }
                                else {
                                    echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                }
                            }
                        }
                    }
                }
              }
            }
            parallel sim_nodes
        }
    }
}

if (test_edma) {
    all_tests['Test EDMA Driver'] = {
        stage('Test EDMA Driver') {
            node(get_task_label(task: 'runtime', xilinx_version: default_xilinx_version)) {

                echo "Test EDMA Driver"
                checkout scm

                String test = "sdk/tests/test_edma.py"
                String report_file = "test_edma.xml"

                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                    """
                } catch (exc) {
                    echo "${test} failed."
                    junit healthScaleFactor: 10.0, testResults: report_file
                    input message: "EDMA driver test failed. Click Proceed or Abort when you are done debugging on the instance."
                    throw exc
                } finally {
                    if (fileExists(report_file)) {
                        junit healthScaleFactor: 10.0, testResults: report_file
                        // archiveArtifacts artifacts: "sdk/tests/fio_dma_tools/scripts/*.csv", fingerprint: true
                        //archiveArtifacts artifacts: "/var/log/messages", fingerprint: true
                    }
                    else {
                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                    }
                }
            }
        }
    }
}

if (test_non_root_access) {
    all_tests['Test non-root access to FPGA tools'] = {
        stage('Test non-root access to FPGA tools') {
            node(get_task_label(task: 'runtime', xilinx_version: default_xilinx_version)) {

                echo "Test non-root access to FPGA tools"
                checkout scm

                String test = "sdk/tests/test_non_root_access.py"
                String report_file = "test_non_root_access.xml"

                try {
                    sh """
                        export AWS_FPGA_ALLOW_NON_ROOT=y
                        export AWS_FPGA_SDK_OVERRIDE_GROUP=y
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        newgrp fpgauser
                        export SDK_DIR="${WORKSPACE}/sdk"
                        source  $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        python2.7 -m pytest -v $WORKSPACE/${test} --junit-xml $WORKSPACE/${report_file}
                    """
                } catch (exc) {
                    input message: "Non-root access test failed. Click Proceed or Abort when you are done debugging on the instance."
                    throw exc
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }
            }
        }
    }
}

if (test_xdma) {
    all_tests['Test XDMA Driver'] = {
        stage('Test XDMA Driver') {
            node(get_task_label(task: 'runtime', xilinx_version: default_xilinx_version)) {

                echo "Test XDMA Driver"
                checkout scm

                String test = "sdk/tests/test_xdma.py"
                String report_file = "test_xdma.xml"

                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                    """
                } catch (exc) {
                    echo "${test} failed."
                    junit healthScaleFactor: 10.0, testResults: report_file
                    input message: "XDMA driver test failed. Click Proceed or Abort when you are done debugging on the instance."
                    throw exc
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                    //archiveArtifacts artifacts: "sdk/tests/fio_dma_tools/scripts/*.csv", fingerprint: true
                    //archiveArtifacts artifacts: "/var/log/messages", fingerprint: true
                }
            }
        }
    }
}

if(disable_runtime_tests) {
    echo "Runtime tests disabled. Not running Test Runtime Software stages"
}
else {
    if (test_runtime_software) {
        all_tests['Test Runtime Software'] = {

            stage('Test Runtime Software') {
                def nodes = [:]
                def node_types = ['runtime', 'runtime_all_slots']
                for (n in node_types) {
                    node_type = n
                    for (x in runtime_sw_cl_names) {
                        String cl_name = x
                        String node_name = "Undefined"
                        switch (node_type) {
                            case "runtime":
                                node_name = "Test Runtime Software ${default_xilinx_version} f1.2xl ${cl_name}"
                                break;
                            case "runtime_all_slots":
                                node_name = "Test Runtime Software ${default_xilinx_version} f1.16xl ${cl_name}"
                                break;
                        }
                        String node_label = get_task_label(task: node_type, xilinx_version: default_xilinx_version)
                        nodes[node_name] = {
                            node(node_label) {
                                String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_precompiled_${cl_name}"
                                String report_file = "test_runtime_software_${cl_name}.xml"
                                checkout scm

                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                                        python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                    """
                                } finally {
                                    if (fileExists(report_file)) {
                                        junit healthScaleFactor: 10.0, testResults: report_file
                                    }
                                    else {
                                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                    }
                                }
                            }
                        }
                    }
                }
                parallel nodes
            }
        }
    }
}


if (test_dcp_recipes) {
    all_tests['Test DCP Recipes'] = {
        stage('Test DCP Recipes') {
            def nodes = [:]
            for (version in xilinx_versions) {
                String xilinx_version = version

                for (cl in dcp_recipe_cl_names) {
                    String cl_name = cl
                    for (s in dcp_recipe_scenarios) {
                        String recipe_scenario = s
                        String node_name = "Test DCP Recipe ${cl_name}[${xilinx_version}-${recipe_scenario}]"
                        nodes[node_name] = {
                            node(get_task_label(task: 'dcp_gen', xilinx_version: xilinx_version)) {
                                String test_name = "test_${cl_name}[${xilinx_version}-${recipe_scenario}]"
                                String report_file = "test_dcp_recipe_${cl_name}[${xilinx_version}-${recipe_scenario}].xml"
                                String build_dir = "hdk/cl/examples/${cl_name}/build"
                                checkout scm
                                try {
                                    sh """
                                      set -e
                                      source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                      python2.7 -m pytest -s -v hdk/tests/test_gen_dcp.py::TestGenDcp::${test_name} --junit-xml $WORKSPACE/${report_file} --xilinxVersion ${xilinx_version}
                                      """
                                } catch(exc) {
                                    echo "${test_name} DCP generation failed: archiving results"
                                    archiveArtifacts artifacts: "${build_dir}/**", fingerprint: true
                                    throw exc
                                } finally {
                                    if (fileExists(report_file)) {
                                        junit healthScaleFactor: 10.0, testResults: report_file
                                    }
                                    else {
                                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                    }
                                }
                            }
                        }
                    }
                }
            }

            parallel nodes
        }
    }
}

if (test_hdk_fdf) {
    // Top level stage for FDF
    // Each CL will have its own parallel FDF stage under this one.
    all_tests['HDK_FDF'] = {
        stage('HDK FDF') {
            def fdf_stages = [:]
            for (version in xilinx_versions) {
                String xilinx_version = version

                for (x in fdf_test_names) {
                    String fdf_test_name = x
                    String cl_name = ""

                    if (fdf_test_name.contains('[')) {
                        def split_test = fdf_test_name.split(/\[/)
                        def test_base_name = split_test[0]
                        def test_args = split_test[1]

                        fdf_test_name = "$test_base_name[$xilinx_version-$test_args"
                        cl_name = test_base_name
                    }

                    String fdf_stage_name = "FDF ${xilinx_version} ${fdf_test_name}"
                    fdf_stages[fdf_stage_name] = {
                        stage(fdf_stage_name) {
                            echo "Generate DCP for ${xilinx_version} ${fdf_test_name}"
                            String build_dir = "hdk/cl/examples/${cl_name}/build"
                            String dcp_stash_name = "dcp_tarball_${fdf_test_name}_${xilinx_version}".replaceAll(/[\[\]]/, "_")
                            String dcp_stash_dir = "${build_dir}/checkpoints/to_aws"
                            String afi_stash_name = "afi_${fdf_test_name}_${xilinx_version}".replaceAll(/[\[\]]/, "_")
                            String afi_stash_dir = "${build_dir}/create_afi"
                            echo "dcp_stash_name=${dcp_stash_name}"
                            echo "afi_stash_name=$afi_stash_name}"
                            node(get_task_label(task: 'dcp_gen', xilinx_version: xilinx_version)) {
                                String test = "hdk/tests/test_gen_dcp.py::TestGenDcp::test_${fdf_test_name}"
                                String report_file = "test_dcp_${fdf_test_name}_${xilinx_version}.xml"
                                checkout scm
                                // Clean out the to_aws directory to make sure there are no artifacts left over from a previous build
                                try {
                                    sh """
                                        rm -rf ${dcp_stash_dir}
                                    """
                                } catch(exc) {
                                    // Ignore any errors
                                    echo "Failed to clean ${dcp_stash_dir}"
                                }
                                try {
                                    sh """
                                      set -e
                                      source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                      python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file} --xilinxVersion ${xilinx_version}
                                      """
                                } catch (exc) {
                                    echo "${fdf_test_name} DCP generation failed: archiving results"
                                    archiveArtifacts artifacts: "${build_dir}/**", fingerprint: true
                                    throw exc
                                } finally {
                                    if (fileExists(report_file)) {
                                        junit healthScaleFactor: 10.0, testResults: report_file
                                    }
                                    else {
                                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                    }
                                }
                                try {
                                    stash name: dcp_stash_name, includes: "${dcp_stash_dir}/**"
                                } catch (exc) {
                                    echo "stash ${dcp_stash_name} failed:\n${exc}"
                                }
                            }
                            node(get_task_label(task: 'create_afi', xilinx_version: xilinx_version)) {
                                echo "Generate AFI for ${xilinx_version} ${fdf_test_name}"
                                checkout scm
                                String test = "hdk/tests/test_create_afi.py::TestCreateAfi::test_${fdf_test_name}"
                                String report_file = "test_create_afi_${fdf_test_name}_${xilinx_version}.xml"
                                // Clean out the stash directories to make sure there are no artifacts left over from a previous build
                                try {
                                    sh """
                                        rm -rf ${dcp_stash_dir}
                                    """
                                } catch(exc) {
                                    // Ignore any errors
                                    echo "Failed to clean ${dcp_stash_dir}"
                                }
                                try {
                                    sh """
                                        rm -rf ${afi_stash_dir}
                                    """
                                } catch(exc) {
                                    // Ignore any errors
                                    echo "Failed to clean ${afi_stash_dir}"
                                }
                                try {
                                    unstash name: dcp_stash_name
                                } catch (exc) {
                                    echo "unstash ${dcp_stash_name} failed:\n${exc}"
                                    //throw exc
                                }
                                try {
                                    // There is a Xilinx bug that causes the following error during hdk_setup.sh if multiple
                                    // processes are doing it at the same time:
                                    // WARNING: [Common 17-1221] Tcl app 'xsim' is out of date for this release. Please run tclapp::reset_tclstore and reinstall the app.
                                    // ERROR: [Common 17-685] Unable to load Tcl app xilinx::xsim
                                    // ERROR: [Common 17-69] Command failed: ERROR: [Common 17-685] Unable to load Tcl app xilinx::xsim
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                                        python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file} --xilinxVersion ${xilinx_version}
                                    """
                                } catch (exc) {
                                    echo "${fdf_test_name} AFI generation failed: archiving results"
                                    archiveArtifacts artifacts: "${build_dir}/to_aws/**", fingerprint: true
                                    throw exc
                                } finally {
                                    if (fileExists(report_file)) {
                                        junit healthScaleFactor: 10.0, testResults: report_file
                                    }
                                    else {
                                        echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                    }
                                }
                                try {
                                    stash name: afi_stash_name, includes: "${afi_stash_dir}/**"
                                } catch (exc) {
                                    echo "stash ${afi_stash_name} failed:\n${exc}"
                                    //throw exc
                                }
                            }

                            if(disable_runtime_tests) {
                                echo "Runtime tests disabled. Not running runtime ${fdf_test_name}"
                            }
                            else {
                                node(get_task_label(task: 'runtime', xilinx_version: xilinx_version)) {
                                    String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_${fdf_test_name}"
                                    String report_file = "test_load_afi_${fdf_test_name}_${xilinx_version}.xml"
                                    checkout scm
                                    echo "Test AFI for ${xilinx_version} ${fdf_test_name} on F1 instance"
                                    // Clean out the stash directories to make sure there are no artifacts left over from a previous build
                                    try {
                                        sh """
                                            rm -rf ${afi_stash_dir}
                                        """
                                    } catch(exc) {
                                        // Ignore any errors
                                        echo "Failed to clean ${afi_stash_dir}"
                                    }
                                    try {
                                        unstash name: afi_stash_name
                                    } catch (exc) {
                                        echo "unstash ${afi_stash_name} failed:\n${exc}"
                                        //throw exc
                                    }
                                    try {
                                        sh """
                                            set -e
                                            source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                                            python2.7 -m pytest -v ${test} --junit-xml $WORKSPACE/${report_file} --xilinxVersion ${xilinx_version}
                                        """
                                    } finally {
                                        if (fileExists(report_file)) {
                                            junit healthScaleFactor: 10.0, testResults: report_file
                                        }
                                        else {
                                            echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                                        }
                                    }
                                }
                            } //else
                        } // stage(
                    }
                } // for (x in fdf_test_names)

            } //  for (xilinx_version in xilinx_versions) {

            parallel fdf_stages
        }
    }
}

//=============================================================================
// SDAccel Tests
//=============================================================================

if (test_sdaccel_scripts) {
    all_tests['Test SDAccel Scripts'] = {
        stage('Test SDAccel Scripts') {
            def nodes = [:]

            for (def xilinx_version in xilinx_versions) {

                String node_label = get_task_label(task: 'source_scripts', xilinx_version: xilinx_version)
                String node_name = "Test SDAccel Scripts ${xilinx_version}"
                nodes[node_name] = {
                    node(node_label) {
                        String report_file = "test_sdaccel_scripts_${xilinx_version}.xml"
                        checkout scm
                        try {
                            sh """
                                set -e
                                source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                                python2.7 -m pytest -v $WORKSPACE/SDAccel/tests/test_sdaccel_scripts.py --junit-xml $WORKSPACE/${report_file}
                            """
                        } finally {
                            if (fileExists(report_file)) {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                            else {
                                echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                            }
                        }
                    }
                }
            }
            parallel nodes
        }
    }
}

if (test_helloworld_sdaccel_example_fdf || test_all_sdaccel_examples_fdf) {
    all_tests['Run SDAccel Tests'] = {
        String sdaccel_examples_list = 'sdaccel_examples_list.json'

        def sdaccel_all_version_stages = [:]

        for (def version in xilinx_versions) {

            String xilinx_version = version
            String sdaccel_base_stage_name = "SDx FDF $xilinx_version"
            String sdaccel_find_stage_name = "SDx Find tests $xilinx_version"

            sdaccel_all_version_stages[sdaccel_base_stage_name] = {
                stage (sdaccel_find_stage_name) {

                    node(get_task_label(task: 'find_tests', xilinx_version: xilinx_version)) {

                        checkout scm
                        String report_file = "test_find_sdaccel_examples_${xilinx_version}.xml"

                        try {
                            sh """
                                rm -rf ${sdaccel_examples_list}
                            """
                        } catch(error) {
                            // Ignore any errors
                            echo "Failed to clean ${sdaccel_examples_list}"
                        }

                        try {
                            sh """
                                set -e
                                source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                python2.7 -m pytest -v $WORKSPACE/SDAccel/tests/test_find_sdaccel_examples.py --junit-xml $WORKSPACE/${report_file}
                            """
                        } catch (exc) {
                            echo "Could not find tests. Please check the repository."
                            throw exc
                        } finally {
                            if (fileExists(report_file)) {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                            else {
                                echo "Pytest wasn't run for stage. Report file not generated: ${report_file}"
                            }
                        }

                        // Only run the hello world test by default
                        //def example_map = [ 'Hello_World': 'SDAccel/examples/xilinx/getting_started/host/helloworld_ocl' ]
                        def example_map = sdaccel_example_default_map.get(xilinx_version)

                        // Run all examples when parameter set
                        if (test_all_sdaccel_examples_fdf) {
                            example_map = readJSON file: sdaccel_examples_list
                        }

                        def sdaccel_build_stages = [:]

                        for ( def e in entrySet(example_map) ) {

                            String test_key = e.key
                            def dsa_map_for_version = dsa_map.get(xilinx_version)

                            // dsa = [ 4DDR: 4ddr ]
                            for ( def dsa in entrySet(dsa_map_for_version) ) {

                                String build_name = "SDx ${e.key}_${dsa.value}_${xilinx_version}"
                                String example_path = e.value

                                String dsa_name = dsa.key
                                String dsa_rte_name = dsa.value

                                String sw_emu_stage_name      = "SDx SW_EMU ${build_name}"
                                String hw_emu_stage_name      = "SDx HW_EMU ${build_name}"
                                String hw_stage_name          = "SDx HW ${build_name}"
                                String create_afi_stage_name  = "SDx AFI ${build_name}"
                                String run_example_stage_name = "SDx RUN ${build_name}"

                                String sw_emu_report_file      = "sdaccel_sw_emu_${e.key}_${dsa.value}_${xilinx_version}.xml"
                                String hw_emu_report_file      = "sdaccel_hw_emu_${e.key}_${dsa.value}_${xilinx_version}.xml"
                                String hw_report_file          = "sdaccel_hw_${e.key}_${dsa.value}_${xilinx_version}.xml"
                                String create_afi_report_file  = "sdaccel_create_afi_${e.key}_${dsa.value}_${xilinx_version}.xml"
                                String run_example_report_file = "sdaccel_run_${e.key}_${dsa.value}_${xilinx_version}.xml"

                                String description_file = "${example_path}/description.json"
                                def description_json = ["targets":["hw","hw_emu","sw_emu"]]

                                try {
                                    description_json = readJSON file: description_file
                                }
                                catch (exc) {
                                    echo "Could not read the file: ${description_file}"
                                    throw exc
                                }

                                boolean test_sw_emu_supported = true

                                if(description_json["targets"]) {
                                    if(description_json["targets"].contains("sw_emu")) {
                                        test_sw_emu_supported = true
                                        echo "Description file ${description_file} has target sw_emu"
                                    }
                                    else {
                                        test_sw_emu_supported = false
                                        echo "Description file ${description_file} does not have target sw_emu"
                                    }
                                }
                                else {
                                    echo "Description json did not have a 'target' key"
                                }

                                sdaccel_build_stages[build_name] = {
                                    if(test_sw_emu_supported) {
                                        stage(sw_emu_stage_name) {
                                            node(get_task_label(task: 'sdaccel_builds', xilinx_version: xilinx_version)) {

                                                checkout scm

                                                try {
                                                    sh """
                                                        set -e
                                                        source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                                        export AWS_PLATFORM=\$AWS_PLATFORM_${dsa_name}
                                                        python2.7 -m pytest -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_sw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${sw_emu_report_file} --timeout=14400 --rteName ${dsa_rte_name} --xilinxVersion ${xilinx_version}
                                                    """
                                                } catch (error) {
                                                    echo "${sw_emu_stage_name} SW EMU Build generation failed"
                                                    archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                                    throw error
                                                } finally {
                                                    if (fileExists(sw_emu_report_file)) {
                                                        junit healthScaleFactor: 10.0, testResults: sw_emu_report_file
                                                    }
                                                    else {
                                                        echo "Pytest wasn't run for stage. Report file not generated: ${sw_emu_report_file}"
                                                    }
                                                    sh """
                                                        set -e
                                                        sudo git reset --hard
                                                        sudo git clean -fdx
                                                    """
                                                }
                                            }
                                        }
                                    }

                                    stage(hw_emu_stage_name) {
                                        node(get_task_label(task: 'sdaccel_builds', xilinx_version: xilinx_version)) {

                                            checkout scm

                                            try {
                                                sh """
                                                    set -e
                                                    source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                                    export AWS_PLATFORM=\$AWS_PLATFORM_${dsa_name}
                                                    python2.7 -m pytest -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_hw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_emu_report_file} --timeout=21600 --rteName ${dsa_rte_name} --xilinxVersion ${xilinx_version}
                                                """
                                            } catch (error) {
                                                echo "${hw_emu_stage_name} HW EMU Build generation failed"
                                                archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                                throw error
                                            } finally {
                                                if (fileExists(hw_emu_report_file)) {
                                                    junit healthScaleFactor: 10.0, testResults: hw_emu_report_file
                                                }
                                                else {
                                                    echo "Pytest wasn't run for stage. Report file not generated: ${hw_emu_report_file}"
                                                }
                                                sh """
                                                    set -e
                                                    sudo git reset --hard
                                                    sudo git clean -fdx
                                                """
                                            }
                                        }
                                    }

                                    stage(hw_stage_name) {
                                        node(get_task_label(task: 'sdaccel_builds', xilinx_version: xilinx_version)) {

                                            checkout scm

                                            try {
                                                sh """
                                                    set -e
                                                    source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                                    export AWS_PLATFORM=\$AWS_PLATFORM_${dsa_name}
                                                    python2.7 -m pytest -s -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_hw_build --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_report_file} --timeout=36000 --rteName ${dsa_rte_name} --xilinxVersion ${xilinx_version}
                                                """
                                            } catch (error) {
                                                echo "${hw_stage_name} HW Build generation failed"
                                                archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                                throw error
                                            } finally {
                                                if (fileExists(hw_report_file)) {
                                                    junit healthScaleFactor: 10.0, testResults: hw_report_file
                                                }
                                                else {
                                                    echo "Pytest wasn't run for stage. Report file not generated: ${hw_report_file}"
                                                }
                                                sh """
                                                    set -e
                                                    sudo git reset --hard
                                                    sudo git clean -fdx
                                                """
                                            }
                                        }
                                    }

                                    stage(create_afi_stage_name) {
                                        node(get_task_label(task: 'create_afi', xilinx_version: xilinx_version)) {

                                            checkout scm
                                            try {
                                                sh """
                                                    set -e
                                                    source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                                    export AWS_PLATFORM=\$AWS_PLATFORM_${dsa_name}
                                                    python2.7 -m pytest -s -v $WORKSPACE/SDAccel/tests/test_create_sdaccel_afi.py::TestCreateSDAccelAfi::test_create_sdaccel_afi --examplePath ${example_path} --junit-xml $WORKSPACE/${create_afi_report_file} --timeout=18000 --rteName ${dsa_rte_name} --xilinxVersion ${xilinx_version}
                                                """
                                            } catch (error) {
                                                echo "${create_afi_stage_name} Create AFI failed"
                                                archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                                throw error
                                            } finally {

                                                if (fileExists(create_afi_report_file)) {
                                                    junit healthScaleFactor: 10.0, testResults: create_afi_report_file
                                                }
                                                else {
                                                    echo "Pytest wasn't run for stage. Report file not generated: ${create_afi_report_file}"
                                                }

                                                String to_aws_dir = "${example_path}/to_aws"

                                                if (fileExists(to_aws_dir)) {
                                                    sh "rm -rf ${to_aws_dir}"
                                                }
                                                sh """
                                                    set -e
                                                    sudo git reset --hard
                                                    sudo git clean -fdx
                                                """
                                            }
                                        }
                                    }

                                    stage(run_example_stage_name) {

                                        if(disable_runtime_tests) {
                                            echo "Runtime tests disabled. Not running ${run_example_stage_name}"
                                        }
                                        else {
                                            node(get_task_label(task: 'runtime', xilinx_version: xilinx_version)) {

                                                checkout scm
                                                try {
                                                    sh """
                                                        set -e
                                                        source $WORKSPACE/shared/tests/bin/setup_test_runtime_sdaccel_env.sh
                                                        export AWS_PLATFORM=\$AWS_PLATFORM_${dsa_name}
                                                        python2.7 -m pytest -v $WORKSPACE/SDAccel/tests/test_run_sdaccel_example.py::TestRunSDAccelExample::test_run_sdaccel_example --examplePath ${example_path} --junit-xml $WORKSPACE/${run_example_report_file} --timeout=14400 --rteName ${dsa_rte_name} --xilinxVersion ${xilinx_version}
                                                    """
                                                } catch (error) {
                                                    echo "${run_example_stage_name} Runtime example failed"
                                                    archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                                    input message: "SDAccel Runtime test failed. Click Proceed or Abort when you are done debugging on the instance."
                                                    throw error
                                                } finally {
                                                    if (fileExists(run_example_report_file)) {
                                                        junit healthScaleFactor: 10.0, testResults: run_example_report_file
                                                    }
                                                    else {
                                                        echo "Pytest wasn't run for stage. Report file not generated: ${run_example_report_file}"
                                                    }
                                                    sh """
                                                        set -e
                                                        sudo git reset --hard
                                                        sudo git clean -fdx
                                                    """
                                                }
                                            }
                                        } //else

                                    }

                                } // sdaccel_build_stages[ e.key ]

                            } //for ( def dsa in entrySet(dsa_map_for_version) ) {
                        } // for ( e in list_map )

                        parallel sdaccel_build_stages
                    }
                }
            }
        } //for (def xilinx_version in xilinx_versions) {
        parallel sdaccel_all_version_stages
    }
}

//=============================================================================
// SDK Tests
//=============================================================================


// Run the tests here
parallel all_tests
