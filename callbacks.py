import util as U
import inspect

callback_names = map(
    lambda a: '__callback{}__'.format(a),
    U.make_fresh())

# assumes:
#     function definition saved in file
#     function defined using def
#     function declaration is one line
#
# desugars
#
#     a, b, .. <- f(x, y, ..)
#     s
#
# into (k fresh)
#
#     def k(a, b, ..):
#         s
#     return f(x, y, .., k)
#
#
# and
#
#     for a, b, .. in l1 <- l:
#         s1
#         c, d, .. <- f(x, y, ..)
#         s2
#         e, f, .. <- g(z, w, ..)
#         s3
#     s
#
# into (loop, l2, k, k1 fresh)
#
#     def loop(l2, l1=()):
#         if l != ():
#             (a, b, ..), l = l[0], l[1:]
#             s1*
#             def k(c, d, ..):
#                 s2*
#                 def k1(e, f, ..):
#                     s3*
#                 return g(z, w, .., k1)
#             return f(x, y, .., k)
#         else:
#             s
#     loop(tuple(l))
#
# where s1*, s2*, s3* are s1, s2, s3 with
#
#     yield a, b, ..
#
# replaced by
#
#     return loop(l, l1 + ((a, b, ..),))
#
# if there are no yields, insert
#
#     return loop(l, l1 + (None,))
#
# at the end of s3.
def callbacks(context):
    def decorator(f):
        lines = inspect.getsource(f).split('\n')
        lines = lines[1:] # drop decorator header
        decl, lines = lines[0], lines[1:] # grab declaration

        def indent(lines, level=4):
            space= ' ' * level
            return [space + l for l in lines]

        def is_callback(line):
            return ' <- ' in line

        def indent_level(s):
            return len(s) - len(s.lstrip()) if s != '' else 1 << 64

        def next_dedent(lines, level, strict=False):
            return next(i
                for i, l in enumerate([*map(indent_level, lines)] + [-1])
                if l < level or (strict and l == level))

        def maximally_dedent(lines):
            level = min(map(indent_level, lines))
            return [s[level:] for s in lines]

        def is_for(line):
            if 'for' not in line:
                return False
            line = line[line.index('for') + 3:]
            if 'in' not in line:
                return False
            line = line[line.index('in') + 2:]
            if not is_callback(line):
                return False
            return True

        def go_for(line, body, rest):
            tokens = [t
                for token in line.split()
                for t in [token.replace(',', '').replace(':', '')]
                if t != '']
            i = tokens.index('in')
            values = tokens[1:i]
            tokens = tokens[i+1:]
            l1, captures, l = tokens[0], tokens[1:-2], tokens[-1]
            values = ', '.join(values)
            captures = ''.join(a + ', ' for a in captures)

            loop, l2 = next(callback_names), next(callback_names)

            level = min(map(indent_level, body + rest))
            body = maximally_dedent(body)
            rest = maximally_dedent(rest)

            found_yield = False
            for i, line in enumerate(body):
                if len(line.split()) < 1 or line.split()[0] != 'yield':
                    continue
                found_yield = True
                _, yielded = line.split(None, 1)
                body[i] = (' ' * indent_level(line) +
                    f'return {loop}({l2}, {captures} {l1} + (({yielded}),))')
            if not found_yield:
                body.append(f'return {loop}({l2}, {captures} {l1} + (None,))')
            header = \
                [f'def {loop}({l2}, {captures} {l1}=()):'] + indent(
                    [f'if {l2} != ():'] + indent(
                        [f'({values}), {l2} = {l2}[0], {l2}[1:]']))
            return indent(
                header +
                indent(indent(go(body))) +
                indent(['else:']) +
                indent(indent(go(rest))) +
                [f'return {loop}(tuple({l}), {captures} {l1}=())'], level)

        def go(lines):
            if lines == []:
                return []
            line, lines = lines[0], lines[1:]

            if not is_callback(line):
                return [line] + go(lines)

            level = indent_level(line)

            if is_for(line):
                i = next_dedent(lines, level, strict=True)
                body, rest = lines[:i], lines[i:]
                return go_for(line, body, rest)

            i = next_dedent(lines, level)
            body, rest = lines[:i], lines[i:]

            args, call = line.split(' <- ')
            args = args.strip()
            call = call.strip()

            callback = next(callback_names)
            header = f'def {callback}({args}):'
            footer = 'return {}{}{})'.format(
                call[:-1],
                (', ' if call[-2] != '(' else ''),
                callback)

            return (
                [level * ' ' + header] +
                go(indent(body)) +
                [level * ' ' + footer] +
                go(rest))

        src = maximally_dedent([decl] + go(lines))
        src = '\n'.join(src)

        #print(src)
        exec(src, context)
        return context[f.__name__]

    return decorator

if __name__ == '__main__':
    def g(a, callback):
        return callback(a, a + 1)

    @callbacks(globals())
    def f(l, p=True):
        for a, b in l1 <- l:
            b, c <- g(a)
            if p:
                d, e <- g(b)
                yield {b: (d, e)}
            else:
                q = p
                yield {a: (b, c), 'p': q}
            h, i <- g(c)
            q = not p
            yield {a: (b, c)}, {b: (d, e)}, {c: (h, i), '¬ p': q}
        return l1

    print(f([(1, 2), (3, 4), (5, 6)], False))
    # ==> (({1: (1, 2)}, {1: (1, 2)}, {2: (2, 3)}), ({3: (3, 4)}, {3: (3, 4)}, {4: (4, 5)}),)
