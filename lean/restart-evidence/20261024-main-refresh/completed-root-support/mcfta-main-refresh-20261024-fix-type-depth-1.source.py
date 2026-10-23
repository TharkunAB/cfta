import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
search = root / 'specftacular/src/Specftacular.hs'
text = search.read_text()
before = '''                ( O.option
                    O.auto
                    ( O.long "type-depth"
'''
after = '''                ( O.option
                    ( O.eitherReader $ \\text ->
                        case TR.readMaybe text of
                            Just depth | depth >= 0 -> Right depth
                            _ -> Left "type depth must be a nonnegative integer"
                    )
                    ( O.long "type-depth"
'''
assert text.count(before) == 1
text = text.replace(before, after)
before = '''    givenSig =
        do
            -- Threads write whole diagnostic lines.
'''
after = '''    givenSig =
        do
            when (maybe False (< 0) typeDepthSetting) $
                fail "type depth must be a nonnegative integer"
            -- Threads write whole diagnostic lines.
'''
assert text.count(before) == 1
search.write_text(text.replace(before, after))
utils = root / 'specftacular/src/Specftacular/Utils.hs'
text = utils.read_text()
before = "only the types with at most D levels of constructors and arrows above the\nconstants and the type variables. Without a depth, all the types ('mtau').\n"
after = before + 'A negative depth raises an error.\n'
assert text.count(before) == 1
text = text.replace(before, after)
before = 'mtauWithin (Just depth) comps = go depth\n'
after = '''mtauWithin (Just depth) comps
    | depth < 0 = error "mtauWithin: type depth must be a nonnegative integer"
    | otherwise = go depth
'''
assert text.count(before) == 1
utils.write_text(text.replace(before, after))
subprocess.run(['fourmolu', '--mode', 'inplace', str(search), str(utils)], cwd=root, check=True)
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
print('PASS: negative type depth rejected at the parser, search and grammar entry points.')
