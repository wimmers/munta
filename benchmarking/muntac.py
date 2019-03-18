import os

import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

class Tool(benchexec.tools.template.BaseTool):

    RUNNER = 'benchmarking/runner.sh'

    def executable(self):
        return util.find_executable('ML/muntac')


    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        suffix = ''
        if 'int' in options:
            suffix = '_int'
        elif 'imp' in options:
            suffix = '_imp'
        elif 'ocaml' in options:
            suffix = '_ocaml'
        elif 'mlton' in options:
            suffix = '_mlton'

        num_threads = 1
        if 'num-threads' in options:
            i = options.index('num-threads')
            num_threads=int(options[i + 1])
        
        implementation = 1
        if 'implementation' in options:
            i = options.index('implementation')
            implementation=int(options[i + 1])

        opts = []
        opts += ['-i', str(implementation)]
        opts += ['-n', str(num_threads)]
        
        if 'deadlock' in options:
            opts += ['-dc']

        return [executable + suffix] + opts + ['-m'] + tasks


    def name(self):
        return 'muntac'


    def determine_result(self, returncode, returnsignal, output, isTimeout):
        status = result.RESULT_UNKNOWN
        for line in output:
            if line.startswith('Certificate was rejected'):
                status = result.RESULT_UNSAT
            elif line.startswith('Certificate was accepted'):
                status = result.RESULT_SAT
            elif line.startswith('Invalid input'):
                status = 'PRECOND_ERROR'
            elif line.startswith('Failed to read line from input!'):
                status = 'INPUT_ERROR'
            elif line.startswith('Parse error'):
                status = 'PARSE_ERROR'
            elif line.startswith('Fatal error: exception Out_of_memory'):
                status = 'OUT OF MEMORY'
            elif (returnsignal == 9):
                status = 'TIMEOUT'
        return status

    def get_value_from_output(self, lines, identifier):
        NUM_STRING = '# explored states:'

        result = ''
        if identifier != 'num-states':
            return result
        for line in lines:
            if NUM_STRING in line:
                result = line.strip(NUM_STRING)

        return result 
