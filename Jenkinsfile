#!/usr/bin/env groovy

//=============================================================================
// Pipeline parameters
//=============================================================================
properties([parameters([
    string(name: 'branch', defaultValue: ''),
    booleanParam(name: 'test_markdown_links',   defaultValue: true),
    booleanParam(name: 'test_hdk_scripts',      defaultValue: true),
    booleanParam(name: 'test_sims',             defaultValue: true),
    booleanParam(name: 'test_edma',             defaultValue: true, description: 'Run EDMA unit and perf tests'),
    booleanParam(name: 'test_runtime_software', defaultValue: true, description: 'Test precompiled AFIs'),
    booleanParam(name: 'test_dcp_recipes',      defaultValue: false, description: 'Run DCP generation with all clock recipes and build strategies.'),
    booleanParam(name: 'test_fdf',              defaultValue: true, description: 'Test full developer flow on cl_hello_world and cl_dram_dma'),
    booleanParam(name: 'test_sdaccel_scripts',  defaultValue: true),
    booleanParam(name: 'test_sdaccel_builds',   defaultValue: true),
    booleanParam(name: 'debug_dcp_gen',         defaultValue: false, description: 'Only run FDF on cl_hello_world. Overrides test_*.'),
    booleanParam(name: 'debug_fdf_uram',        defaultValue: false, description: 'Debug the FDF for cl_uram_example.')

])])

//=============================================================================
// Configuration
//=============================================================================
boolean test_markdown_links = params.get('test_markdown_links')
boolean test_hdk_scripts = params.get('test_hdk_scripts')
boolean test_sims = params.get('test_sims')
boolean test_edma = params.get('test_edma')
boolean test_runtime_software = params.get('test_runtime_software')
boolean test_dcp_recipes = params.get('test_dcp_recipes')
boolean test_fdf = params.get('test_fdf')
boolean test_sdaccel_scripts = params.get('test_sdaccel_scripts')
boolean test_sdaccel_builds = params.get('test_sdaccel_builds')

def runtime_sw_cl_names = ['cl_dram_dma', 'cl_hello_world']
def dcp_recipe_cl_names = ['cl_dram_dma', 'cl_hello_world']
def dcp_recipe_scenarios = [
    // Default values are tested in FDF: A0-B0-C0-DEFAULT
    // Fastest clock speeds are: A1-B2-C0
    // Test each clock recipe with the BASIC strategy
    // Test all strategies with highest clock speeds
    '[A1-B1-C1-BASIC]',
    '[A1-B2-C0-BASIC]',
    '[A2-B3-C2-BASIC]',
    '[A1-B4-C3-BASIC]',
    '[A1-B5-C0-BASIC]',
    '[A1-B2-C0-DEFAULT]',
    '[A1-B2-C0-EXPLORE]',
    '[A1-B2-C0-TIMING]',
    '[A1-B2-C0-TIMING]',
    '[A1-B2-C0-CONGESTION]',
    ]
def fdf_test_names = ['cl_dram_dma[A0-B0-C0-DEFAULT]', 'cl_hello_world[A0-B0-C0-DEFAULT]', 'cl_hello_world_vhdl',
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
//=============================================================================
// Globals
//=============================================================================

// Map that contains top level stages
def top_parallel_stages = [:]

// Task to Label map
def task_label = [
    'create-afi':        't2-l-50',
    'simulation':        'c4xl',
    'dcp_gen':           'c4-4xl',
    'runtime':           'f1-2xl',
    'runtime-all-slots': 'f1-16xl',
    'source_scripts':    'c4xl',
    'md_links':          'c4xl',
    'find_tests':        't2-l-50',
    'sdaccel_builds':    'c4-4xl'
]

// Get serializable entry set
@NonCPS def entrySet(m) {m.collect {k, v -> [key: k, value: v]}}


//=============================================================================
// Shared Tests
//=============================================================================

if (test_markdown_links) {
    top_parallel_stages['Test Markdown Links'] = {
        stage('Test Markdown Links') {
            String report_file = 'test_md_links.xml'
            node(task_label.get('md_links')) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        pytest -v $WORKSPACE/shared/tests/test_md_links.py --junit-xml $WORKSPACE/${report_file}
                    """
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }
            }
        }
    }
}

//=============================================================================
// HDK Tests
//=============================================================================

if (test_hdk_scripts) {
    top_parallel_stages['Test HDK Scripts'] = {
        stage('Test HDK Scripts') {
            String report_file = 'test_hdk_scripts.xml'
            node(task_label.get('source_scripts')) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        pytest -v $WORKSPACE/hdk/tests/test_hdk_scripts.py --junit-xml $WORKSPACE/${report_file}
                    """
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }
            }
        }
    }
}

if (test_sims) {
    top_parallel_stages['Run Sims'] = {
        stage('Run Sims') {
            def cl_names = ['cl_dram_dma', 'cl_hello_world']
            def sim_nodes = [:]
            for (x in cl_names) {
                String cl_name = x
                String node_name = "Sims ${cl_name}"
                String key = "test_${cl_name}__"
                String report_file = "test_sims_${cl_name}.xml"
                sim_nodes[node_name] = {
                    node(task_label.get('simulation')) {
                        checkout scm
                        try {
                            sh """
                                set -e
                                source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                pytest -v $WORKSPACE/hdk/tests/simulation_tests/test_sims.py -k \"${key}\" --junit-xml $WORKSPACE/${report_file}
                            """
                        } catch (exc) {
                            echo "${node_name} failed: archiving results"
                            archiveArtifacts artifacts: "hdk/cl/examples/${cl_name}/verif/sim/**", fingerprint: true
                            throw exc
                        } finally {
                            junit healthScaleFactor: 10.0, testResults: report_file
                        }
                    }
                }
            }
            parallel sim_nodes
        }
    }
}

if (test_edma) {
    top_parallel_stages['Test EDMA Driver'] = {
        stage('Test EDMA Driver') {
            node(task_label.get('runtime')) {
                echo "Test EDMA Driver"
                checkout scm
                String report_file = "test_edma.xml"
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                        pytest -v sdk/tests/test_edma.py --junit-xml $WORKSPACE/${report_file}
                    """
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }
            }
        }
    }
}

if (test_runtime_software) {
    top_parallel_stages['Test Runtime Software'] = {
        stage('Test Runtime Software') {
            def nodes = [:]
            def node_types = ['runtime', 'runtime-all-slots']
            for (n in node_types) {
                node_type = n
                for (x in runtime_sw_cl_names) {
                    String cl_name = x
                    String node_name
                    switch (node_type) {
                        case "runtime":
                            node_name = "Test Runtime Software f1.2xl ${cl_name}"
                            break;
                        case "runtime-all-slots":
                            node_name = "Test Runtime Software f1.16xl ${cl_name}"
                            break;
                    }
                    String node_label = task_label.get(node_type)
                    nodes[node_name] = {
                        node(node_label) {
                            String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_precompiled_${cl_name}"
                            String report_file = "test_runtime_software_${cl_name}.xml"
                            checkout scm

                            try {
                                sh """
                                    set -e
                                    source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                                    pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                """
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                        }
                    }
                }
            }
            parallel nodes
        }
    }
}

if (test_dcp_recipes) {
    top_parallel_stages['Test DCP Recipes'] = {
        stage('Test DCP Recipes') {
            def nodes = [:]
            for (cl in dcp_recipe_cl_names) {
                String cl_name = cl
                for (s in dcp_recipe_scenarios) {
                    String recipe_scenario = s
                    String node_name = "Test DCP Recipe ${cl_name}${recipe_scenario}"
                    nodes[node_name] = {
                        node(task_label.get('dcp_gen')) {
                            String test_name = "test_${cl_name}${recipe_scenario}"
                            String report_file = "test_dcp_recipe_${cl_name}${recipe_scenario}.xml"
                            String build_dir = "hdk/cl/examples/${cl_name}/build"
                            checkout scm
                            try {
                                sh """
                                  set -e
                                  source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                  pytest -v hdk/tests/test_gen_dcp.py::TestGenDcp::${test_name} --junit-xml $WORKSPACE/${report_file}
                                  """
                            } catch(exc) {
                                echo "${test_name} DCP generation failed: archiving results"
                                archiveArtifacts artifacts: "${build_dir}/**", fingerprint: true
                                throw exc
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                        }
                    }
                }
            }
            parallel nodes
        }
    }
}

if (test_fdf) {
    // Top level stage for FDF
    // Each CL will have its own parallel FDF stage under this one.
    top_parallel_stages['FDF'] = {
        stage('FDF') {
            def fdf_stages = [:]
            for (x in fdf_test_names) {
                String fdf_test_name = x
                String cl_name
                if (fdf_test_name.startsWith("cl_hello_world[")) {
                    cl_name = "cl_hello_world"
                } else if (fdf_test_name.startsWith("cl_dram_dma[")) {
                    cl_name = "cl_dram_dma"
                } else if (fdf_test_name.startsWith("cl_uram_example[")) {
                    cl_name = "cl_uram_example"
                } else {
                    cl_name = fdf_test_name
                }
                String fdf_stage_name = "FDF ${fdf_test_name}"
                fdf_stages[fdf_stage_name] = {
                    stage(fdf_stage_name) {
                        String build_dir = "hdk/cl/examples/${cl_name}/build"
                        String dcp_stash_name = "dcp_tarball_${fdf_test_name}"
                        String dcp_stash_dir = "${build_dir}/checkpoints/to_aws"
                        String afi_stash_name = "afi_${fdf_test_name}"
                        String afi_stash_dir = "${build_dir}/create-afi"
                        node(task_label.get('dcp_gen')) {
                            String test = "hdk/tests/test_gen_dcp.py::TestGenDcp::test_${fdf_test_name}"
                            String report_file = "test_dcp_${fdf_test_name}.xml"
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
                            echo "Generate DCP for ${fdf_test_name}"
                            try {
                                sh """
                                  set -e
                                  source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                  pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                  """
                            } catch (exc) {
                                echo "${fdf_test_name} DCP generation failed: archiving results"
                                archiveArtifacts artifacts: "${build_dir}/**", fingerprint: true
                                throw exc
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                            try {
                                stash name: dcp_stash_name, includes: "${dcp_stash_dir}/**"
                            } catch (exc) {
                                echo "stash ${dcp_stash_name} failed"
                            }
                        }
                        node(task_label.get('create-afi')) {
                            echo "Generate AFI for ${fdf_test_name}"
                            checkout scm
                            String test = "hdk/tests/test_create_afi.py::TestCreateAfi::test_${fdf_test_name}"
                            String report_file = "test_create_afi_${fdf_test_name}.xml"
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
                                echo "unstash ${dcp_stash_name} failed"
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
                                    pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                """
                            } catch (exc) {
                                echo "${fdf_test_name} AFI generation failed: archiving results"
                                archiveArtifacts artifacts: "${build_dir}/to_aws/**", fingerprint: true
                                throw exc
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                            try {
                                stash name: afi_stash_name, includes: "${afi_stash_dir}/**"
                            } catch (exc) {
                                echo "stash ${afi_stash_name} failed"
                                //throw exc
                            }
                        }
                        node(task_label.get('runtime')) {
                            String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_${fdf_test_name}"
                            String report_file = "test_load_afi_${fdf_test_name}.xml"
                            checkout scm
                            echo "Test AFI for ${fdf_test_name} on F1 instance"
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
                                echo "unstash ${afi_stash_name} failed"
                                //throw exc
                            }
                            try {
                                sh """
                                    set -e
                                    source $WORKSPACE/shared/tests/bin/setup_test_sdk_env.sh
                                    pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                """
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                        }
                    }
                }
            }
            parallel fdf_stages
        }
    }
}

//=============================================================================
// SDAccel Tests
//=============================================================================

if (test_sdaccel_scripts) {
    top_parallel_stages['Test SDAccel Scripts'] = {
        stage('Test SDAccel Scripts') {
            String report_file = 'test_sdaccel_scripts.xml'
            node(task_label.get('source_scripts')) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        pytest -v $WORKSPACE/SDAccel/tests/test_sdaccel_scripts.py --junit-xml $WORKSPACE/${report_file}
                    """
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }
            }
        }
    }
}

if (test_sdaccel_builds) {
    top_parallel_stages['Run SDAccel Tests'] = {
        def sdaccel_build_stages = [:]
        String sdaccel_examples_list = 'sdaccel_examples_list.json'

        stage ('Find SDAccel tests') {

            String report_file = 'test_find_sdaccel_examples.xml'

            node(task_label.get('find_tests')) {

                checkout scm

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
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        pytest -v $WORKSPACE/SDAccel/tests/test_find_sdaccel_examples.py --junit-xml $WORKSPACE/${report_file}
                    """
                } catch (exc) {
                    echo "Could not find tests. Please check the repository."
                    throw exc
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }

                //def list_map = readJSON file: sdaccel_examples_list
                // Just run the hello world example for now
                def list_map = [ 'Hello_World': 'SDAccel/examples/xilinx/getting_started/host/helloworld_ocl' ]

                for ( def e in entrySet(list_map) ) {

                    String build_name = e.key
                    String example_path = e.value

                    String sw_emu_stage_name      = "SDAccel SW_EMU ${build_name}"
                    String hw_emu_stage_name      = "SDAccel HW_EMU ${build_name}"
                    String hw_stage_name          = "SDAccel HW ${build_name}"
                    String create_afi_stage_name  = "SDAccel AFI ${build_name}"
                    String run_example_stage_name = "SDAccel RUN ${build_name}"

                    String sw_emu_report_file      = "sdaccel_sw_emu_${build_name}.xml"
                    String hw_emu_report_file      = "sdaccel_hw_emu_${build_name}.xml"
                    String hw_report_file          = "sdaccel_hw_${build_name}.xml"
                    String create_afi_report_file  = "sdaccel_create_afi_${build_name}.xml"
                    String run_example_report_file = "sdaccel_run_${build_name}.xml"

                    sdaccel_build_stages[build_name] = {

                        stage(sw_emu_stage_name) {
                            node(task_label.get('sdaccel_builds')) {

                                checkout scm

                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                        pytest -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_sw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${sw_emu_report_file} --timeout=3600

                                    """
                                } catch (error) {
                                    echo "${sw_emu_stage_name} SW EMU Build generation failed"
                                    throw error
                                } finally {
                                    junit healthScaleFactor: 10.0, testResults: sw_emu_report_file
                                }
                            }
                        }

                        stage(hw_emu_stage_name) {
                            node(task_label.get('sdaccel_builds')) {

                                checkout scm

                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                        pytest -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_hw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_emu_report_file} --timeout=3600
                                    """
                                } catch (error) {
                                    echo "${hw_emu_stage_name} HW EMU Build generation failed"
                                    throw error
                                } finally {
                                    junit healthScaleFactor: 10.0, testResults: hw_emu_report_file
                                }
                            }
                        }

                        stage(hw_stage_name) {
                            node(task_label.get('sdaccel_builds')) {

                                checkout scm

                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                        pytest -v $WORKSPACE/SDAccel/tests/test_build_sdaccel_example.py::TestBuildSDAccelExample::test_hw_build --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_report_file} --timeout=25200
                                    """
                                } catch (error) {
                                    echo "${hw_stage_name} HW Build generation failed"
                                    throw error
                                } finally {
                                    junit healthScaleFactor: 10.0, testResults: hw_report_file
                                }
                            }
                        }

                        stage(create_afi_stage_name) {
                            node(task_label.get('create-afi')) {

                                checkout scm
                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                        pytest -v $WORKSPACE/SDAccel/tests/test_create_sdaccel_afi.py::TestCreateSDAccelAfi::test_create_sdaccel_afi --examplePath ${example_path} --junit-xml $WORKSPACE/${create_afi_report_file} --timeout=3600
                                    """
                                } catch (error) {
                                    echo "${create_afi_stage_name} Create AFI failed"
                                    throw error
                                } finally {
                                    junit healthScaleFactor: 10.0, testResults: create_afi_report_file
                                }
                            }
                        }

                        stage(run_example_stage_name) {
                            node(task_label.get('runtime')) {

                                checkout scm
                                try {
                                    sh """
                                        set -e
                                        source $WORKSPACE/shared/tests/bin/setup_test_runtime_sdaccel_env.sh
                                        pytest -v $WORKSPACE/SDAccel/tests/test_run_sdaccel_example.py::TestRunSDAccelExample::test_run_sdaccel_example --examplePath ${example_path} --junit-xml $WORKSPACE/${run_example_report_file} --timeout=3600
                                    """
                                } catch (error) {
                                    echo "${run_example_stage_name} Runtime example failed"
                                    throw error
                                } finally {
                                    junit healthScaleFactor: 10.0, testResults: run_example_report_file
                                }
                            }
                        }


                    } // sdaccel_build_stages[ e.key ]
                } // for ( e in list_map )

                parallel sdaccel_build_stages
            }
        }
    }
}

//=============================================================================
// SDK Tests
//=============================================================================

parallel top_parallel_stages
