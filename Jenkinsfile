#!/usr/bin/env groovy

//=============================================================================
// Pipeline parameters
//=============================================================================
properties([parameters([
    string(name: 'branch', defaultValue: ''),
    booleanParam(name: 'test_markdown_links',   defaultValue: true),
    booleanParam(name: 'test_hdk_scripts',      defaultValue: true),
    booleanParam(name: 'test_sims',             defaultValue: true),
    booleanParam(name: 'test_runtime_software', defaultValue: true),
    booleanParam(name: 'test_fdf',              defaultValue: true),
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
boolean test_runtime_software = params.get('test_runtime_software')
boolean test_fdf = params.get('test_fdf')
boolean test_sdaccel_scripts = params.get('test_sdaccel_scripts')

def runtime_sw_cl_names = ['cl_dram_dma', 'cl_hello_world']
def fdf_cl_names = ['cl_dram_dma', 'cl_hello_world', 'cl_hello_world_vhdl',
    'cl_uram_example_uram_option_2', 'cl_uram_example_uram_option_3', 'cl_uram_example_uram_option_4']

boolean debug_dcp_gen = params.get('debug_dcp_gen')
if (debug_dcp_gen) {
    fdf_cl_names = ['cl_hello_world']
    test_markdown_links = false
    test_sims = false
    test_runtime_software = false
    test_sdaccel_scripts = false
}

boolean debug_fdf_uram = params.get('debug_fdf_uram')
if (debug_fdf_uram) {
    fdf_cl_names = ['cl_uram_example_option_2', 'cl_uram_example_option_3', 'cl_uram_example_option_4']
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
    'create-afi':        'create-afi',
    'simulation':        'c4xl',
    'dcp_gen':           'c4-8xl',
    'runtime':           'f1-2xl',
    'runtime-all-slots': 'f1-16xl',
    'source_scripts':    'c4xl',
    'md_links':          'c4xl',
    'find_tests':        't2-l-1',
    'sdaccel_builds':    'c5-9xl-8'
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
                            raise exc
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

if (test_runtime_software) {
    top_parallel_stages['Test Runtime Software'] = {
        stage('Test Runtime Software') {
            def nodes = [:]
            for (x in runtime_sw_cl_names) {
                String cl_name = x
                String node_name = "Test Runtime Software ${cl_name}"
                String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_precompiled_${cl_name}"
                String report_file = "test_runtime_software_${cl_name}.xml"
                nodes[node_name] = {
                    node(task_label.get('runtime')) {
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
            for (x in fdf_cl_names) {
                String cl_name_with_options = x
                String cl_name = cl_name_with_options
                switch (cl_name_with_options) {
                    case "cl_uram_example_uram_option_2":
                    case "cl_uram_example_uram_option_3":
                    case "cl_uram_example_uram_option_4":
                        cl_name = "cl_uram_example"
                        break;
                }
                String fdf_stage_name = "FDF ${cl_name_with_options}"
                fdf_stages[fdf_stage_name] = {
                    stage(fdf_stage_name) {
                        String build_dir = "hdk/cl/examples/${cl_name}/build"
                        String dcp_stash_name = "dcp_tarball_${cl_name_with_options}"
                        String dcp_stash_dir = "${build_dir}/checkpoints/to_aws"
                        String afi_stash_name = "afi_${cl_name_with_options}"
                        String afi_stash_dir = "${build_dir}/create-afi"
                        node(task_label.get('dcp_gen')) {
                            String test = "hdk/tests/test_gen_dcp.py::TestGenDcp::test_${cl_name_with_options}"
                            String report_file = "test_dcp_${cl_name_with_options}.xml"
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
                            echo "Generate DCP for ${cl_name_with_options}"
                            try {
                                sh """
                                  set -e
                                  source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                  pytest -v ${test} --junit-xml $WORKSPACE/${report_file}
                                  """
                            } catch (exc) {
                                echo "${cl_name_with_options} DCP generation failed: archiving results"
                                archiveArtifacts artifacts: "${build_dir}/**", fingerprint: true
                                raise exc
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
                            echo "Generate AFI for ${cl_name_with_options}"
                            checkout scm
                            String test = "hdk/tests/test_create_afi.py::TestCreateAfi::test_${cl_name_with_options}"
                            String report_file = "test_create_afi_${cl_name_with_options}.xml"
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
                                raise exc
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
                                echo "${cl_name_with_options} AFI generation failed: archiving results"
                                archiveArtifacts artifacts: "${build_dir}/to_aws/**", fingerprint: true
                                raise exc
                            } finally {
                                junit healthScaleFactor: 10.0, testResults: report_file
                            }
                            try {
                                stash name: afi_stash_name, includes: "${afi_stash_dir}/**"
                            } catch (exc) {
                                echo "stash ${afi_stash_name} failed"
                                raise exc
                            }
                        }
                        node(task_label.get('runtime')) {
                            String test = "hdk/tests/test_load_afi.py::TestLoadAfi::test_${cl_name_with_options}"
                            String report_file = "test_load_afi_${cl_name_with_options}.xml"
                            checkout scm
                            echo "Test AFI for ${cl_name_with_options} on F1 instance"
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
                                raise exc
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
        stage ('Find SDACCel tests') {
            String report_file = 'test_find_sdaccel_examples.xml'
            node(task_label.get('find_tests')) {
                checkout scm
                try {
                    sh """
                        set -e
                        source $WORKSPACE/shared/tests/bin/setup_test_env.sh
                        pytest -v $WORKSPACE/SDAccel/tests/test_find_sdaccel_examples.py --junit-xml $WORKSPACE/${report_file}
                    """
                } catch (exc) {
                    echo "Could not find tests. Please check the repository."
                    raise exc
                } finally {
                    junit healthScaleFactor: 10.0, testResults: report_file
                }

                def list_map = readJSON file:'sdaccel_examples_list.json'

                for ( def e in entrySet(list_map) ) {

                    String build_name = e.key
                    String example_path = e.value
                    String stage_name = "SDAccel Build ${build_name}"

                    sdaccel_build_stages[build_name] = {

                        stage(stage_name) {
                            timeout (time: 7, unit: 'HOURS') {
                                node(task_label.get('sdaccel_builds')) {

                                    String sw_emu_report_file = "sdaccel_sw_emu_${build_name}.xml"
                                    String hw_emu_report_file = "sdaccel_hw_emu_${build_name}.xml"
                                    String hw_report_file = "sdaccel_hw_${build_name}.xml"

                                    checkout scm

                                    try {
                                        sh """
                                            set -e
                                            source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                            source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                            pytest -v $WORKSPACE/SDAccel/tests/test_run_sdaccel_examples.py::TestRunSDAccelExamples::test_sw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${sw_emu_report_file}

                                        """
                                    } catch (error) {
                                        echo "${stage_name} SW EMU Build generation failed"
                                    } finally {
                                        junit healthScaleFactor: 10.0, testResults: sw_emu_report_file
                                    }

                                    try {
                                        sh """
                                            set -e
                                            source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                            source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                            pytest -v $WORKSPACE/SDAccel/tests/test_run_sdaccel_examples.py::TestRunSDAccelExamples::test_hw_emu --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_emu_report_file}
                                        """
                                    } catch (error) {
                                        echo "${stage_name} HW EMU Build generation failed"
                                    } finally {
                                        junit healthScaleFactor: 10.0, testResults: hw_emu_report_file
                                    }

                                    try {
                                        sh """
                                            set -e
                                            source $WORKSPACE/shared/tests/bin/setup_test_hdk_env.sh
                                            source $WORKSPACE/shared/tests/bin/setup_test_build_sdaccel_env.sh
                                            pytest -v $WORKSPACE/SDAccel/tests/test_run_sdaccel_examples.py::TestRunSDAccelExamples::test_hw_build --examplePath ${example_path} --junit-xml $WORKSPACE/${hw_report_file}
                                        """
                                    } catch (error) {
                                        echo "${stage_name} HW Build generation failed"
                                        archiveArtifacts artifacts: "${example_path}/**", fingerprint: true
                                        raise error
                                    } finally {
                                        junit healthScaleFactor: 10.0, testResults: hw_report_file
                                    }
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
