

def consts_to_string(consts):
    result = ""
    for const in consts:
        if not str(type(const).__name__) == "code":
            result = result + '(' + str(type(const).__name__) + ':' + str(const) + ')'
        else:
            result = result + '(code:{@' + code_object_to_string(const) + '})'
    return result

def names_to_string(names):
    result = ""
    for name in names:
        result = result + name + ','
    return result

def format_code(code):
    result = "";
    for i in code:
        if ord(i) < 16: result = result + '\\\\x0' + hex(ord(i))[2:]
        else: result = result + '\\\\x' + hex(ord(i))[2:]
    return result

def code_object_to_string(codeobject):
    args = codeobject.co_argcount
    nlocals = codeobject.co_nlocals
    stacksize = codeobject.co_stacksize
    flags = codeobject.co_flags
    code = format_code(codeobject.co_code)
    consts = codeobject.co_consts
    names = codeobject.co_names
    varnames = codeobject.co_varnames
    freevars = codeobject.co_freevars
    cellvars = codeobject.co_cellvars
    filename = codeobject.co_filename
    name = codeobject.co_name
    firstlineno = codeobject.co_firstlineno
    lnotab = format_code(codeobject.co_lnotab)
    return str(args) + '@' + str(nlocals) + '@' + str(stacksize) + '@' + str(flags) + '@' + code + '@' + consts_to_string(consts) + '@' + names_to_string(names) + '@' + names_to_string(varnames) + '@' + names_to_string(freevars) + '@' + names_to_string(cellvars) + '@' + filename + '@' + name + '@' + str(firstlineno) + '@' + lnotab + '@'

def function_to_string(fun):
    return code_object_to_string(fun.__code__)

def export_function(function, argtypes, returns, multithreading=False, table=False):
    name = function.__code__.co_name;
    argc = function.__code__.co_argcount
    argnames = function.__code__.co_varnames
    language = " language PYTHON_MAP" if multithreading else " language P"
    if len(argtypes) != argc:
        raise Exception('The length of the argument types does not match the amount of function arguments.')
    argstr = ""
    for i in range(0, argc): argstr = argstr + argnames[i] + ' ' + argtypes[i] + ','
    retstr = returns[0]
    if len(returns) > 1 or table:
        retstr = "table (";
        for i in returns: retstr = retstr + i + ','
        retstr= retstr[:len(retstr)-1] + ")";
    export = 'CREATE FUNCTION ' + name + '(' + argstr[:len(argstr)-1] + ') returns ' + retstr + language + '{@' + function_to_string(function) + '};'
    for ch in export:
        if ord(ch) == 0:
            raise Exception("Zero byte!");
    return(export)

import multiprocessing
import numpy
import platform
import os
import sys
python_version = str(sys.version_info.major) + '.' + str(sys.version_info.minor) + '.' + str(sys.version_info.micro)
numpy_version = numpy.version.version
amount_of_cores = str(multiprocessing.cpu_count())
main_memory = str(-1)
try: main_memory = str(int(os.popen("cat /proc/meminfo | grep MemTotal | awk '{ print $2 }'").read().translate(None, ' \n\t')) / 1000 ** 2)
except: pass
os_name = ' '.join(platform.dist())

def format_headers(measurement_xaxis, measurement_yaxis, measurement_zaxis = None):
    return 'Python Ver\tNumpy Ver\tCPU Cores\tMain Memory (GB)\tOS\t' + measurement_xaxis + '\t' + measurement_yaxis + ('\t' + measurement_zaxis if measurement_zaxis is not None else '') + '\n'

def format_output(measurement_x, measurement_y, measurement_z = None):
    return python_version + '\t' + numpy_version + '\t' + amount_of_cores + '\t' + main_memory + '\t' + os_name + '\t' + str(measurement_x) + '\t' + str(measurement_y) + ('\t' + str(measurement_z) if measurement_z is not None else '') + '\n'

import os
import sys
import time

# The arguments are
# [1] => Type of test ['INPUT', 'OUTPUT']
# [2] => Output file name
# [3] => Number of tests for each value
# [4+] => List of input values
arguments = sys.argv
if (len(arguments) <= 4):
    print("Too few arguments provided.")
    quit()

output_file = os.path.join(os.getcwd(), arguments[2])
test_count = int(arguments[3])
max_retries = 15

import monetdb.sql
# Try to connect to the database
# We try a couple of times because starting up the database takes some time, so it might fail the first few times
for i in range(0, max_retries):
    try:
        connection = monetdb.sql.connect(username="monetdb", password="monetdb", hostname="localhost", database="demo")
        break
    except:
        time.sleep(3)
    connection = None

if connection is None:
    print("Failed to connect to MonetDB Server (mserver5) in " + str(max_retries) + " attempts.")
    sys.exit(1)

cursor = connection.cursor()


if str(arguments[1]).lower() == "input" or str(arguments[1]).lower() == "input-map":
    # Input testing

    # First create a function that generates the desired input size (in MB) and pass it to the database
    def generate_integers(mb):
        import random
        import math
        byte_size = mb * 1000 * 1000
        integer_size_byte = 4
        max_int = math.pow(2,31) - 1
        min_int = -max_int
        integer_count = int(byte_size / integer_size_byte)
        integers = numpy.zeros(integer_count, dtype=numpy.int32)
        for i in range(0, integer_count):
            integers[i] = random.randint(min_int, max_int)
        return integers

    cursor.execute(export_function(generate_integers, ['integer'], ['i integer'], table=True))

    # Our import test function returns a single boolean value and doesn't do anything with the actual input
    # This way the input loading is the only relevant factor in running time, because the time taken for function execution/output handling is constant
    def import_test(inp):
        return(True)

    cursor.execute(export_function(import_test, ['integer'], ['boolean'], multithreading=str(arguments[1]).lower() == "input-map"))

    import time
    f = open(output_file + '.tsv', "w+")
    f.write(format_headers('Data Size (MB)', 'Time (s)'))
    mb = []
    for i in range(4, len(arguments)):
        mb.append(float(arguments[i]))

    for size in mb:
        start = time.time()
        cursor.execute('create temporary table integers as SELECT * FROM generate_integers(' + str(size) + ') with data;')
        end = time.time()
        for i in range(0,test_count):
            start = time.time()
            cursor.execute('select import_test(i) from integers;');
            cursor.fetchall();
            end = time.time()
            f.write(format_output(size, end - start))
            f.flush()
        cursor.execute('drop table integers;')
    f.close()

    cursor.execute('drop function generate_integers');
    cursor.execute('drop function import_test');
    cursor.execute('rollback')
elif str(arguments[1]).lower() == "output":
    # output testing

    # we use a single scalar as input (the amount of MB to generate) so the input handling is fast
    # we do some computation (namely creating the output array) but that should only be a single malloc call, and should be negligible compared to the copying
    # that malloc call is also the same for both zero copy and copy, so it shouldn't make any difference in the comparison
    def generate_output(mb):
        byte_size = mb * 1000 * 1000
        integer_size_byte = 4
        integer_count = int(byte_size / integer_size_byte)
        integers = numpy.zeros(integer_count, dtype=numpy.int32)
        return integers

    cursor.execute(export_function(generate_output, ['float'], ['i integer'], table=True))

    f = open(output_file + '.tsv', "w+")
    f.write(format_headers('Data Size (MB)', 'Time (s)'))
    mb = []
    for i in range(4, len(arguments)):
        mb.append(float(arguments[i]))

    for size in mb:
        for i in range(0,test_count):
            start = time.time()
            cursor.execute('select count(*) from generate_output(' + str(size) + ');');
            cursor.fetchall();
            end = time.time()
            f.write(format_output(size, end - start))
            f.flush()
    f.close()

    cursor.execute('drop function generate_output');
    cursor.execute('rollback')

elif str(arguments[1]).lower() == "string_samelength" or str(arguments[1]).lower() == "string_extremeunicode":
    if str(arguments[1]).lower() == "string_samelength":
        def generate_strings_samelength(mb, length):
            def random_string(length):
                import random
                import string
                result = ""
                for i in range(0, length):
                    result += random.choice(string.printable)
                return result
            import random
            import math
            byte_size = mb * 1000 * 1000
            string_size_byte = length
            string_count = int(byte_size / string_size_byte)
            strings = numpy.zeros(string_count, dtype='S' + str(length))
            for i in range(0, string_count):
                strings[i] = random_string(length)
            return strings
        cursor.execute(export_function(generate_strings_samelength, ['float', 'integer'], ['i string'], table=True))
    else:
        def generate_strings_samelength(mb, length):
            def random_string(length):
                import random
                import string
                result = unicode('')
                for i in range(0, length):
                    result += random.choice(string.printable)
                return result
            import random
            import math
            byte_size = mb * 1000 * 1000
            string_size_byte = length
            string_count = int(byte_size / string_size_byte)
            strings = numpy.zeros(string_count, dtype='U' + str(length))
            for i in range(0, string_count - 1):
                strings[i] = random_string(length)
            strings[string_count - 1] = random_string(length - 1) + unichr(0x100)
            return strings
        cursor.execute(export_function(generate_strings_samelength, ['float', 'integer'], ['i string'], table=True))

    mb = []
    lens = []
    for i in range(4, len(arguments)):
        tple = arguments[i].translate(None, '()').split(',')
        mb.append(float(tple[0]))
        lens.append(int(tple[1]))

    def import_test(inp):
        return(True)

    cursor.execute(export_function(import_test, ['string'], ['boolean']))

    f = open(output_file + '.tsv', "w+")
    f.write(format_headers('Data Size (MB)', 'String Length (Characters)', 'Time (s)'))
    for j in range(0,len(mb)):
        size = mb[j]
        length = lens[j]
        start = time.time()
        cursor.execute('create table strings as SELECT * FROM generate_strings_samelength(' + str(size) + ',' + str(length) + ') with data;')
        end = time.time()
        for i in range(0,test_count):
            start = time.time()
            cursor.execute('select import_test(i) from strings;');
            cursor.fetchall();
            end = time.time()
            f.write(format_output(size, length, end - start))
            f.flush()
        cursor.execute('drop table strings;')
    f.close()

    cursor.execute('drop function generate_strings_samelength');
    cursor.execute('drop function import_test');
    cursor.execute('rollback')
elif str(arguments[1]).lower() == "string_extremelength":
    def generate_strings_extreme(extreme_length, string_count):
        def random_string(length):
            import random
            import string
            result = ""
            for i in range(0, length):
                result += random.choice(string.printable)
            return result
        import random
        import math
        result = numpy.array([], dtype=object)
        result = numpy.append(result, random_string(extreme_length))
        for i in range(0, string_count - 1):
            result = numpy.append(result, random_string(1))
        return result

    cursor.execute(export_function(generate_strings_extreme, ['integer', 'integer'], ['i string'], table=True))

    extreme_lengths = []
    string_counts = []
    for i in range(4, len(arguments)):
        tple = arguments[i].translate(None, '()').split(',')
        extreme_lengths.append(float(tple[0]))
        string_counts.append(int(tple[1]))

    def import_test(inp):
        return(True)

    cursor.execute(export_function(import_test, ['string'], ['boolean']))

    f = open(output_file + '.tsv', "w+")
    f.write(format_headers('(Strings)', 'Extreme Length (Characters)', 'Time (s)'))
    for j in range(0,len(extreme_lengths)):
        str_len = extreme_lengths[j]
        str_count = string_counts[j]
        start = time.time()
        cursor.execute('create table strings as SELECT * FROM generate_strings_extreme(' + str(str_len) + ',' + str(str_count) + ') with data;')
        end = time.time()
        for i in range(0,test_count):
            start = time.time()
            cursor.execute('select import_test(i) from strings;');
            cursor.fetchall();
            end = time.time()
            f.write(format_output(str_count, str_len, end - start))
            f.flush()
        cursor.execute('drop table strings;')
    f.close()

    cursor.execute('drop function generate_strings_extreme');
    cursor.execute('drop function import_test');
    cursor.execute('rollback')
else:
    print("Unrecognized test type \"" + arguments[1] + "\", exiting...")
    sys.exit(1)

