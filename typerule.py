import util as U
import inspect

callback_names = map(
    lambda a: '__callback{}__'.format(a),
    U.make_fresh())

# assumes:
#   function definition saved in file
#   function defined using def
#   function declaration is one line
def typerule(context):
    def decorator(f):
        lines = inspect.getsource(f).split('\n')
        lines = lines[1:] # drop decorator header
        decl, lines = lines[0], lines[1:] # grab declaration

        def indent(lines):
            return ['    ' + l for l in lines]

        def is_callback(line):
            return ' <- ' in line

        def indent_level(s):
            return len(s) - len(s.lstrip()) if s != '' else 1 << 64

        def go(lines):
            if lines == []:
                return []
            line, lines = lines[0], lines[1:]
            if not is_callback(line):
                return [line] + go(lines)
            args, call = line.split(' <- ')
            leading_space = indent_level(args)
            args = args.strip()
            call = call.strip()
            i = next(i
                for i, level in enumerate([*map(indent_level, lines)] + [0])
                if level < leading_space)
            body, rest = lines[:i], lines[i:]
            callback = next(callback_names)
            header = 'def {}({}):'.format(callback, args)
            footer = 'return {}, {})'.format(call[:-1], callback)
            return (
                [leading_space * ' ' + header] +
                go(indent(body)) +
                [leading_space * ' ' + footer] +
                go(rest))

        src = [decl] + go(lines)
        leading_space = min(len(s) - len(s.lstrip()) for s in src if s.strip() != '')
        src = [s[leading_space:] for s in src]
        src = '\n'.join(src)

        #print(src)
        exec(src, context)
        return context[f.__name__]

    return decorator

if __name__ == '__main__':
    def g(a, callback):
        return callback(a + 1, a + 2)

    @typerule
    def f(a):
        b, c <- g(a)
        return b + c

    print(f)
    print(f(3))
