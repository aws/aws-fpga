#!/usr/bin/env groovy

// basic declarative pipeline

pipeline {
    agent {  
        label "f1"
    }
    stages {
        stage('build') {
            steps {
                sh 'shared/tests/jenkins.sh'
            }
        }
    }
    post {
        always {
            archiveArtifacts artifacts: 'logs/*', fingerprint: true
        }
    }
}