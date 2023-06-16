def expect(want, have):
  if want != have:
    raise Exception(f'\nWant: {want}\nHave: {have}')
def raises(thunk):
  result = None
  try: result = thunk()
  except: pass
  if result is not None:
    raise ValueError(f'Instead of exception got {result}')