First ask for all the errors:

  $ $MERLIN single errors -filename test.ml < test.ml
  {
    "class": "return",
    "value": [],
    "notifications": []
  }

Notice that the second type error is not returned, as it happens after the first
syntax error.

Now let's just ask for typing errors:

  $ $MERLIN single errors -lexing false -parsing false -filename test.ml < test.ml
  {
    "class": "return",
    "value": [],
    "notifications": []
  }

And let's also try filtering out type errors:

  $ $MERLIN single errors -typing false -filename test.ml < test.ml
  {
    "class": "return",
    "value": [],
    "notifications": []
  }
