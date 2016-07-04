(function(f) {

  'use strict';

  /* istanbul ignore else */
  if (typeof module === 'object' && typeof module.exports === 'object') {
    module.exports = f(require('sanctuary-type-classes'));
  } else if (typeof define === 'function' && define.amd != null) {
    define(['sanctuary-type-classes'], f);
  } else {
    self.sanctuaryDef = f(self.sanctuaryTypeClasses);
  }

}(function(Z) {

  'use strict';

  var $ = {};

  var MAX_SAFE_INTEGER = Math.pow(2, 53) - 1;
  var MIN_SAFE_INTEGER = -MAX_SAFE_INTEGER;

  //  Left :: a -> Either a b
  var Left = function Left(x) {
    return {
      '@@type': 'sanctuary-def/Either',
      isLeft: true,
      isRight: false,
      'fantasy-land/chain': function(f) { return Left(x); },
      'fantasy-land/map': function(f) { return Left(x); },
      value: x
    };
  };

  //  Right :: b -> Either a b
  var Right = function Right(x) {
    return {
      '@@type': 'sanctuary-def/Either',
      isLeft: false,
      isRight: true,
      'fantasy-land/chain': function(f) { return f(x); },
      'fantasy-land/map': function(f) { return Right(f(x)); },
      value: x
    };
  };

  //  K :: a -> b -> a
  var K = function(x) { return function(y) { return x; }; };

  //  always :: a -> (-> a)
  var always = function(x) { return function() { return x; }; };

  //  always2 :: a -> (b, c) -> a
  var always2 = function(x) { return function(y, z) { return x; }; };

  //  has :: (String, Object) -> Boolean
  var has = function(k, o) {
    return Object.prototype.hasOwnProperty.call(o, k);
  };

  //  id :: a -> a
  var id = function(x) { return x; };

  //  isEmpty :: Array a -> Boolean
  var isEmpty = function(xs) { return xs.length === 0; };

  //  isPrefix :: Array a -> Array a -> Boolean
  var isPrefix = function(candidate) {
    return function(xs) {
      if (candidate.length > xs.length) return false;
      for (var idx = 0; idx < candidate.length; idx += 1) {
        if (candidate[idx] !== xs[idx]) return false;
      }
      return true;
    };
  };

  //  last :: Array a -> a
  var last = function(xs) { return xs[xs.length - 1]; };

  //  or :: (Array a, Array a) -> Array a
  var or = function(xs, ys) { return isEmpty(xs) ? ys : xs; };

  //  range :: (Number, Number) -> Array Number
  var range = function(start, stop) {
    var result = [];
    for (var n = start; n < stop; n += 1) result.push(n);
    return result;
  };

  //  strRepeat :: (String, Integer) -> String
  var strRepeat = function(s, times) {
    return Array(times + 1).join(s);
  };

  //  r :: Char -> String -> String
  var r = function(c) {
    return function(s) {
      return strRepeat(c, s.length);
    };
  };

  //  _ :: String -> String
  var _ = r(' ');

  //  stripOutermostParens :: String -> String
  var stripOutermostParens = function(s) {
    return s.slice('('.length, -')'.length);
  };

  //  trimTrailingSpaces :: String -> String
  var trimTrailingSpaces = function(s) {
    return s.replace(/[ ]+$/gm, '');
  };

  //  unless :: (Boolean, (a -> a), a) -> a
  var unless = function(bool, f, x) {
    return bool ? x : f(x);
  };

  //  when :: (Boolean, (a -> a), a) -> a
  var when = function(bool, f, x) {
    return bool ? f(x) : x;
  };

  //  wrap :: String -> String -> String -> String
  var wrap = function(prefix) {
    return function(suffix) {
      return function(s) {
        return prefix + s + suffix;
      };
    };
  };

  //  q :: String -> String
  var q = wrap('\u2018')('\u2019');

  //  stripNamespace :: String -> String
  var stripNamespace = function(s) { return s.slice(s.indexOf('/') + 1); };

  //  createType :: ... -> Type
  var createType = function(
    typeName,   // :: String
    name,       // :: String
    format,     // :: (String -> String, String -> String -> String) -> String
    test,       // :: Any -> Boolean
    keys,       // :: Array String
    types       // :: StrMap { extractor :: a -> Array b, type :: Type }
  ) {
    var validate = function(x) {
      if (!test(x)) return Left({value: x, propPath: []});
      for (var idx = 0; idx < keys.length; idx += 1) {
        var k = keys[idx];
        var t = types[k];
        for (var idx2 = 0, ys = t.extractor(x); idx2 < ys.length; idx2 += 1) {
          var result = t.type.validate(ys[idx2]);
          if (result.isLeft) {
            var value = result.value.value;
            var propPath = Z.concat([k], result.value.propPath);
            return Left({value: value, propPath: propPath});
          }
        }
      }
      return Right(x);
    };

    return {
      '@@type': 'sanctuary-def/Type',
      _test: function(x) { return validate(x).isRight; },
      format: format,
      keys: keys,
      name: name,
      toString: always(format(id, K(id))),
      type: typeName,
      types: types,
      validate: validate
    };
  };

  var BINARY        = 'BINARY';
  var ENUM          = 'ENUM';
  var FUNCTION      = 'FUNCTION';
  var INCONSISTENT  = 'INCONSISTENT';
  var NULLARY       = 'NULLARY';
  var RECORD        = 'RECORD';
  var UNARY         = 'UNARY';
  var UNKNOWN       = 'UNKNOWN';
  var VARIABLE      = 'VARIABLE';

  //  Unknown :: Type
  var Unknown = $.Unknown =
  createType(UNKNOWN, '', always2('???'), K(true), [], {});

  //  Inconsistent :: Type
  var Inconsistent =
  createType(INCONSISTENT, '', always2('???'), K(false), [], {});

  //  TypeVariable :: String -> Type
  $.TypeVariable = function(name) {
    return createType(VARIABLE, name, always2(name), K(true), [], {});
  };

  //  UnaryTypeVariable :: String -> Type -> Type
  $.UnaryTypeVariable = function(name) {
    return function($1) {
      var format = function(outer, inner) {
        return outer('(' + name + ' ') + inner('$1')(String($1)) + outer(')');
      };
      var types = {$1: {extractor: K([]), type: $1}};
      return createType(VARIABLE, name, format, K(true), ['$1'], types);
    };
  };

  //  NullaryType :: (String, (x -> Boolean)) -> Type
  var NullaryType = $.NullaryType = function(name, test) {
    var format = function(outer, inner) {
      return outer(stripNamespace(name));
    };
    return createType(NULLARY, name, format, test, [], {});
  };

  //  UnaryType :: (String, (x -> Boolean), (t a -> Array a)) -> Type -> Type
  var UnaryType = $.UnaryType = function(name, test, _1) {
    return function($1) {
      var format = function(outer, inner) {
        return outer('(' + stripNamespace(name) + ' ') +
               inner('$1')(String($1)) + outer(')');
      };
      var types = {$1: {extractor: _1, type: $1}};
      return createType(UNARY, name, format, test, ['$1'], types);
    };
  };

  //  UnaryType.from :: Type -> (Type -> Type)
  UnaryType.from = function(t) {
    return UnaryType(t.name, t._test, t.types.$1.extractor);
  };

  //  BinaryType ::
  //    (String, (x -> Boolean), (t a b -> Array a), (t a b -> Array b)) ->
  //      (Type, Type) -> Type
  var BinaryType = $.BinaryType = function(name, test, _1, _2) {
    return function($1, $2) {
      var format = function(outer, inner) {
        return outer('(' + stripNamespace(name) + ' ') +
               inner('$1')(String($1)) + outer(' ') +
               inner('$2')(String($2)) + outer(')');
      };
      var types = {$1: {extractor: _1, type: $1},
                   $2: {extractor: _2, type: $2}};
      return createType(BINARY, name, format, test, ['$1', '$2'], types);
    };
  };

  //  BinaryType.xprod :: (Type, Array Type, Array Type) -> Array Type
  BinaryType.xprod = function(t, $1s, $2s) {
    var specialize = BinaryType(t.name,
                                t._test,
                                t.types.$1.extractor,
                                t.types.$2.extractor);
    var $types = [];
    $1s.forEach(function($1) {
      $2s.forEach(function($2) {
        $types.push(specialize($1, $2));
      });
    });
    return $types;
  };

  //  $$type :: a -> String
  var $$type = function $$type(x) {
    return x != null && $$type(x['@@type']) === 'String' ?
      x['@@type'] :
      Object.prototype.toString.call(x).slice('[object '.length, -']'.length);
  };

  //  $$typeEq :: String -> a -> Boolean
  var $$typeEq = function(name) {
    return function(x) {
      return $$type(x) === name;
    };
  };

  //  type0 :: String -> Type
  var type0 = function(name) {
    return NullaryType(name, $$typeEq(name));
  };

  //  type1 :: (String, (t a -> Array a)) -> Type -> Type
  var type1 = function(name, _1) {
    return UnaryType(name, $$typeEq(name), _1);
  };

  //  EnumType :: Array Any -> Type
  var EnumType = $.EnumType = function(members) {
    var format = function(outer, inner) {
      return outer('(' + Z.map(Z.toString, members).join(' | ') + ')');
    };

    var test = function(x) {
      return members.some(function(member) { return Z.equals(x, member); });
    };

    return createType(ENUM, '', format, test, [], {});
  };

  //  RecordType :: StrMap Type -> Type
  var RecordType = $.RecordType = function(fields) {
    var keys = Object.keys(fields).sort();

    var invalidFieldNames = keys.filter(function(k) {
      return $$type(fields[k]) !== 'sanctuary-def/Type';
    });
    if (!isEmpty(invalidFieldNames)) {
      throw new TypeError(trimTrailingSpaces(
        'Invalid values\n\n' +
        'The argument to ‘RecordType’ must be an object ' +
          'mapping field name to type.\n\n' +
        'The following mappings are invalid:\n\n' +
        Z.reduce(function(s, k) {
          var v = fields[k];
          return s + '  - ' + Z.toString(k) + ': ' + Z.toString(v) + '\n';
        }, '', invalidFieldNames)
      ));
    }

    var format = function(outer, inner) {
      return wrap(outer('{'))(outer(' }'))(Z.map(function(k) {
        var t = fields[k];
        return outer(' ' + k + ' :: ') +
               unless(t.type === RECORD || isEmpty(t.keys),
                      stripOutermostParens,
                      inner(k)(String(t)));
      }, keys).join(outer(',')));
    };

    var test = function(x) {
      return x != null &&
             keys.every(function(k) { return has(k, x); });
    };

    var $types = {};
    keys.forEach(function(k) {
      $types[k] = {extractor: function(x) { return [x[k]]; }, type: fields[k]};
    });

    return createType(RECORD, '', format, test, keys, $types);
  };

  //  AnyFunction :: Type
  var AnyFunction = type0('Function');

  //  $.Function :: Array Type -> Type
  $.Function = function(types) {
    var format = function(outer, inner) {
      var xs = types.map(function(t, idx) {
        return unless(t.type === RECORD || isEmpty(t.keys),
                      stripOutermostParens,
                      inner('$' + String(idx + 1))(String(t)));
      });
      var parenthesize = wrap(outer('('))(outer(')'));
      return parenthesize(unless(types.length === 2,
                                 parenthesize,
                                 xs.slice(0, -1).join(outer(', '))) +
                          outer(' -> ') +
                          last(xs));
    };

    var $keys = [];
    var $types = {};
    types.forEach(function(t, idx) {
      var k = '$' + String(idx + 1);
      $keys.push(k);
      $types[k] = {extractor: K([]), type: t};
    });

    return createType(FUNCTION, '', format, AnyFunction._test, $keys, $types);
  };

  //  Nullable :: Type -> Type
  $.Nullable = UnaryType(
    'sanctuary-def/Nullable',
    K(true),
    function(nullable) { return nullable === null ? [] : [nullable]; }
  );

  //  StrMap :: Type -> Type
  var StrMap = UnaryType(
    'sanctuary-def/StrMap',
    function(x) { return $.Object._test(x); },
    function(strMap) {
      return Z.map(function(k) { return strMap[k]; },
                   Object.keys(strMap).sort());
    }
  );

  //  applyParameterizedTypes :: Array Type -> Array Type
  var applyParameterizedTypes = function(types) {
    return Z.map(function(x) {
      return typeof x === 'function' ?
        x.apply(null, Z.map(K(Unknown), range(0, x.length))) :
        x;
    }, types);
  };

  //  defaultEnv :: Array Type
  var defaultEnv = $.env = applyParameterizedTypes([
    $.AnyFunction = AnyFunction,
    $.Arguments   = type0('Arguments'),
    $.Array       = type1('Array', id),
    $.Boolean     = type0('Boolean'),
    $.Date        = type0('Date'),
    $.Error       = type0('Error'),
    $.Null        = type0('Null'),
    $.Number      = type0('Number'),
    $.Object      = type0('Object'),
    $.RegExp      = type0('RegExp'),
    $.StrMap      = StrMap,
    $.String      = type0('String'),
    $.Undefined   = type0('Undefined')
  ]);

  //  Any :: Type
  $.Any = NullaryType(
    'sanctuary-def/Any',
    K(true)
  );

  //  Pair :: (Type, Type) -> Type
  $.Pair = BinaryType(
    'sanctuary-def/Pair',
    function(x) { return $$typeEq('Array')(x) && x.length === 2; },
    function(pair) { return [pair[0]]; },
    function(pair) { return [pair[1]]; }
  );

  //  ValidDate :: Type
  $.ValidDate = NullaryType(
    'sanctuary-def/ValidDate',
    function(x) { return $.Date._test(x) && !isNaN(x.valueOf()); }
  );

  //  PositiveNumber :: Type
  $.PositiveNumber = NullaryType(
    'sanctuary-def/PositiveNumber',
    function(x) { return $.Number._test(x) && x > 0; }
  );

  //  NegativeNumber :: Type
  $.NegativeNumber = NullaryType(
    'sanctuary-def/NegativeNumber',
    function(x) { return $.Number._test(x) && x < 0; }
  );

  //  ValidNumber :: Type
  var ValidNumber = $.ValidNumber = NullaryType(
    'sanctuary-def/ValidNumber',
    function(x) { return $.Number._test(x) && !isNaN(x); }
  );

  //  NonZeroValidNumber :: Type
  $.NonZeroValidNumber = NullaryType(
    'sanctuary-def/NonZeroValidNumber',
    function(x) {
      return ValidNumber._test(x) &&
             /* eslint-disable eqeqeq */
             x != 0;
             /* eslint-enable eqeqeq */
    }
  );

  //  FiniteNumber :: Type
  var FiniteNumber = $.FiniteNumber = NullaryType(
    'sanctuary-def/FiniteNumber',
    function(x) { return ValidNumber._test(x) && isFinite(x); }
  );

  //  PositiveFiniteNumber :: Type
  $.PositiveFiniteNumber = NullaryType(
    'sanctuary-def/PositiveFiniteNumber',
    function(x) { return FiniteNumber._test(x) && x > 0; }
  );

  //  NegativeFiniteNumber :: Type
  $.NegativeFiniteNumber = NullaryType(
    'sanctuary-def/NegativeFiniteNumber',
    function(x) { return FiniteNumber._test(x) && x < 0; }
  );

  //  NonZeroFiniteNumber :: Type
  $.NonZeroFiniteNumber = NullaryType(
    'sanctuary-def/NonZeroFiniteNumber',
    function(x) {
      return FiniteNumber._test(x) &&
             /* eslint-disable eqeqeq */
             x != 0;
             /* eslint-enable eqeqeq */
    }
  );

  //  Integer :: Type
  var Integer = $.Integer = NullaryType(
    'sanctuary-def/Integer',
    function(x) {
      return ValidNumber._test(x) &&
             /* eslint-disable eqeqeq */
             Math.floor(x) == x &&
             /* eslint-enable eqeqeq */
             x >= MIN_SAFE_INTEGER &&
             x <= MAX_SAFE_INTEGER;
    }
  );

  //  PositiveInteger :: Type
  $.PositiveInteger = NullaryType(
    'sanctuary-def/PositiveInteger',
    function(x) { return Integer._test(x) && x > 0; }
  );

  //  NegativeInteger :: Type
  $.NegativeInteger = NullaryType(
    'sanctuary-def/NegativeInteger',
    function(x) { return Integer._test(x) && x < 0; }
  );

  //  NonZeroInteger :: Type
  $.NonZeroInteger = NullaryType(
    'sanctuary-def/NonZeroInteger',
    function(x) {
      return Integer._test(x) &&
             /* eslint-disable eqeqeq */
             x != 0;
             /* eslint-enable eqeqeq */
    }
  );

  //  RegexFlags :: Type
  $.RegexFlags = EnumType(['', 'g', 'i', 'm', 'gi', 'gm', 'im', 'gim']);

  //  Type :: Type
  var Type = type0('sanctuary-def/Type');

  //  TypeClass :: Type
  var TypeClass = type0('sanctuary-type-classes/TypeClass');

  //  arity :: (Number, Function) -> Function
  var arity = function(n, f) {
    return (
      n === 0 ?
        function() {
          return f.apply(this, arguments);
        } :
      n === 1 ?
        function($1) {
          return f.apply(this, arguments);
        } :
      n === 2 ?
        function($1, $2) {
          return f.apply(this, arguments);
        } :
      n === 3 ?
        function($1, $2, $3) {
          return f.apply(this, arguments);
        } :
      n === 4 ?
        function($1, $2, $3, $4) {
          return f.apply(this, arguments);
        } :
      n === 5 ?
        function($1, $2, $3, $4, $5) {
          return f.apply(this, arguments);
        } :
      n === 6 ?
        function($1, $2, $3, $4, $5, $6) {
          return f.apply(this, arguments);
        } :
      n === 7 ?
        function($1, $2, $3, $4, $5, $6, $7) {
          return f.apply(this, arguments);
        } :
      n === 8 ?
        function($1, $2, $3, $4, $5, $6, $7, $8) {
          return f.apply(this, arguments);
        } :
      // else
        function($1, $2, $3, $4, $5, $6, $7, $8, $9) {
          return f.apply(this, arguments);
        }
    );
  };

  //  numArgs :: Number -> String
  var numArgs = function(n) {
    switch (n) {
      case  0:  return  'zero arguments';
      case  1:  return   'one argument';
      case  2:  return   'two arguments';
      case  3:  return 'three arguments';
      case  4:  return  'four arguments';
      case  5:  return  'five arguments';
      case  6:  return   'six arguments';
      case  7:  return 'seven arguments';
      case  8:  return 'eight arguments';
      case  9:  return  'nine arguments';
      default:  return  n + ' arguments';
    }
  };

  //  _determineActualTypes :: ... -> Array Type
  var _determineActualTypes = function recur(
    loose,          // :: Boolean
    env,            // :: Array Type
    types,          // :: Array Type
    seen,           // :: Array Object
    values          // :: Array Any
  ) {
    var refine = function(types, value) {
      var seen$;
      if (typeof value === 'object' && value != null ||
          typeof value === 'function') {
        //  Abort if a circular reference is encountered; add the current
        //  object to the list of seen objects otherwise.
        if (seen.indexOf(value) >= 0) return [];
        seen$ = Z.concat(seen, [value]);
      } else {
        seen$ = seen;
      }
      return Z.chain(function(t) {
        return (
          t.name === 'sanctuary-def/Nullable' || !t._test(value) ?
            [] :
          t.type === UNARY ?
            Z.map(UnaryType.from(t),
                  recur(loose, env, env, seen$, t.types.$1.extractor(value))) :
          t.type === BINARY ?
            BinaryType.xprod(
              t,
              t.types.$1.type.type === UNKNOWN ?
                recur(loose, env, env, seen$, t.types.$1.extractor(value)) :
                [t.types.$1.type],
              t.types.$2.type.type === UNKNOWN ?
                recur(loose, env, env, seen$, t.types.$2.extractor(value)) :
                [t.types.$2.type]
            ) :
          // else
            [t]
        );
      }, types);
    };

    return isEmpty(values) ?
      [Unknown] :
      or(Z.reduce(refine, types, values), loose ? [Inconsistent] : []);
  };

  //  rejectInconsistent :: Array Type -> Array Type
  var rejectInconsistent = function(types) {
    return types.filter(function(t) {
      return t.type !== INCONSISTENT && t.type !== UNKNOWN;
    });
  };

  //  determineActualTypesStrict ::
  //    (Array Type, Array Type, Array Any) -> Array Type
  var determineActualTypesStrict = function(env, types, values) {
    var types$ = _determineActualTypes(false, env, types, [], values);
    return rejectInconsistent(types$);
  };

  //  determineActualTypesLoose ::
  //    (Array Type, Array Type, Array Any) -> Array Type
  var determineActualTypesLoose = function(env, types, values) {
    var types$ = _determineActualTypes(true, env, types, [], values);
    return rejectInconsistent(types$);
  };

  //  TypeVarMap = StrMap { types :: Array Type
  //                      , valuesByPath :: StrMap (Array Any) }
  //
  //  PropPath = Array (Number | String)

  //  updateTypeVarMap :: ... -> TypeVarMap
  var updateTypeVarMap = function(
    env,            // :: Array Type
    typeVarMap,     // :: TypeVarMap
    typeVar,        // :: Type
    index,          // :: Integer
    propPath,       // :: PropPath
    values          // :: Array Any
  ) {
    var $typeVarMap = {};
    for (var typeVarName in typeVarMap) {
      var entry = typeVarMap[typeVarName];
      var $entry = {types: entry.types.slice(0), valuesByPath: {}};
      for (var k in entry.valuesByPath) {
        $entry.valuesByPath[k] = entry.valuesByPath[k].slice(0);
      }
      $typeVarMap[typeVarName] = $entry;
    }
    if (!has(typeVar.name, $typeVarMap)) {
      $typeVarMap[typeVar.name] = {types: env.slice(0), valuesByPath: {}};
    }

    var key = JSON.stringify(Z.concat([index], propPath));
    if (!has(key, $typeVarMap[typeVar.name].valuesByPath)) {
      $typeVarMap[typeVar.name].valuesByPath[key] = [];
    }

    values.forEach(function(value) {
      $typeVarMap[typeVar.name].valuesByPath[key].push(value);
      $typeVarMap[typeVar.name].types = Z.chain(
        function(t) {
          var xs;
          var invalid = !test(env, t, value);
          return (
            invalid ?
              [] :
            typeVar.keys.length === 1 ?
              [t].filter(function(t) {
                return (
                  !isEmpty(t.keys) &&
                  t.type !== RECORD &&
                  (isEmpty(xs = t.types[last(t.keys)].extractor(value))
                   || !isEmpty(determineActualTypesStrict(env, env, xs)))
                );
              }) :
            t.type === UNARY ?
              t.types.$1.type.type === UNKNOWN &&
              !isEmpty(xs = t.types.$1.extractor(value)) ?
                Z.map(UnaryType.from(t),
                      determineActualTypesStrict(env, env, xs)) :
                [t] :
            t.type === BINARY ?
              BinaryType.xprod(
                t,
                t.types.$1.type.type === UNKNOWN &&
                !isEmpty(xs = t.types.$1.extractor(value)) ?
                  determineActualTypesStrict(env, env, xs) :
                  [t.types.$1.type],
                t.types.$2.type.type === UNKNOWN &&
                !isEmpty(xs = t.types.$2.extractor(value)) ?
                  determineActualTypesStrict(env, env, xs) :
                  [t.types.$2.type]
              ) :
            // else
              [t]
          );
        },
        $typeVarMap[typeVar.name].types
      );
    });

    return $typeVarMap;
  };

  //  underlineTypeVars :: ... -> String
  var underlineTypeVars = function(
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    valuesByPath    // :: StrMap (Array Any)
  ) {
    //  Note: Sorting these keys lexicographically is not "correct", but it
    //  does the right thing for indexes less than 10.
    var paths = Z.map(JSON.parse, Object.keys(valuesByPath).sort());
    return underline(
      name,
      constraints,
      expTypes,
      K(K(_)),
      function(index) {
        return function(f) {
          return function(t) {
            return function(propPath) {
              var indexedPropPath = Z.concat([index], propPath);
              return function(s) {
                if (t.type === VARIABLE) {
                  var key = JSON.stringify(indexedPropPath);
                  var exists = has(key, valuesByPath);
                  return (exists && !isEmpty(valuesByPath[key]) ? f : _)(s);
                } else {
                  return unless(paths.some(isPrefix(indexedPropPath)), _, s);
                }
              };
            };
          };
        };
      }
    );
  };

  //  _satisfactoryTypes ::
  //    ... -> Either Error { typeVarMap :: TypeVarMap, types :: Array Type }
  var _satisfactoryTypes = function(
    env,            // :: Array Type
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    index           // :: Integer
  ) {
    return function recur(
      typeVarMap,   // :: TypeVarMap
      expType,      // :: Type
      values,       // :: Array Any
      propPath      // :: PropPath
    ) {
      if (!values.every(expType._test)) {
        return Left(new TypeError('Invalid value'));
      }
      switch (expType.type) {

        case VARIABLE:
          var typeVarName = expType.name;
          if (has(typeVarName, constraints)) {
            var typeClasses = constraints[typeVarName];
            for (var idx = 0; idx < values.length; idx += 1) {
              for (var idx2 = 0; idx2 < typeClasses.length; idx2 += 1) {
                if (!typeClasses[idx2].test(values[idx])) {
                  return Left(typeClassConstraintViolation(
                    env,
                    name,
                    constraints,
                    expTypes,
                    typeClasses[idx2],
                    index,
                    propPath,
                    values[idx],
                    typeVarMap
                  ));
                }
              }
            }
          }

          var typeVarMap$ = updateTypeVarMap(env,
                                             typeVarMap,
                                             expType,
                                             index,
                                             propPath,
                                             values);

          var okTypes = typeVarMap$[typeVarName].types;
          return isEmpty(okTypes) && !isEmpty(values) ?
            Left(typeVarConstraintViolation(
              env,
              name,
              constraints,
              expTypes,
              index,
              propPath,
              typeVarMap$[typeVarName].valuesByPath
            )) :
            Z.reduce(function(e, t) {
              return isEmpty(expType.keys) || isEmpty(t.keys) ?
                e :
                Z.chain(function(r) {
                  var $1 = expType.types[expType.keys[0]].type;
                  var k = last(t.keys);
                  var innerValues = Z.chain(t.types[k].extractor, values);
                  return Z.reduce(function(e, x) {
                    return Z.chain(function(r) {
                      return $1.type === VARIABLE || test(env, $1, x) ?
                        Right(r) :
                        Left(invalidValue(env,
                                          name,
                                          constraints,
                                          expTypes,
                                          index,
                                          Z.concat(propPath, [k]),
                                          x));
                    }, e);
                  }, Right(r), innerValues);
                }, e);
            }, Right({typeVarMap: typeVarMap$, types: okTypes}), okTypes);

        case UNARY:
          return Z.map(
            function(result) {
              return {
                typeVarMap: result.typeVarMap,
                types: Z.map(UnaryType.from(expType),
                             or(result.types, [expType.types.$1.type]))
              };
            },
            recur(typeVarMap,
                  expType.types.$1.type,
                  Z.chain(expType.types.$1.extractor, values),
                  Z.concat(propPath, ['$1']))
          );

        case BINARY:
          return Z.chain(
            function(result) {
              var $1s = result.types;
              return Z.map(
                function(result) {
                  var $2s = result.types;
                  return {
                    typeVarMap: result.typeVarMap,
                    types: BinaryType.xprod(expType,
                                            or($1s, [expType.types.$1.type]),
                                            or($2s, [expType.types.$2.type]))
                  };
                },
                recur(result.typeVarMap,
                      expType.types.$2.type,
                      Z.chain(expType.types.$2.extractor, values),
                      Z.concat(propPath, ['$2']))
              );
            },
            recur(typeVarMap,
                  expType.types.$1.type,
                  Z.chain(expType.types.$1.extractor, values),
                  Z.concat(propPath, ['$1']))
          );

        default:
          return Right({typeVarMap: typeVarMap,
                        types: determineActualTypesStrict(env, env, values)});
      }
    };
  };

  //  satisfactoryTypes :: ... -> Either Error (Array Type)
  var satisfactoryTypes = function(
    env,            // :: Array Type
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    typeVarMap,     // :: TypeVarMap
    value,          // :: Any
    index           // :: Integer
  ) {
    var result = expTypes[index].validate(value);
    return result.isLeft ?
      Left(invalidValue(env,
                        name,
                        constraints,
                        expTypes,
                        index,
                        result.value.propPath,
                        result.value.value)) :
      Z.chain(function(value) {
        var f = _satisfactoryTypes(env, name, constraints, expTypes, index);
        return f(typeVarMap, expTypes[index], [value], []);
      }, result);
  };

  //  test :: (Array Type, Type, Any) -> Boolean
  var test = $.test = function(_env, t, x) {
    var env = applyParameterizedTypes(_env);
    var f = _satisfactoryTypes(env, 'name', {}, [t], 0);
    return f({}, t, [x], [], []).isRight;
  };

  //  checkValue :: ... -> Undefined
  var checkValue = function(
    env,                // :: Array Type
    name,               // :: String
    constraints,        // :: StrMap (Array TypeClass)
    expTypes,           // :: Array Type
    $typeVarMapBox,     // :: Box TypeVarMap
    index,              // :: Integer
    propPath,           // :: PropPath
    t,                  // :: Type
    value               // :: Any
  ) {
    if (t.type === VARIABLE) {
      $typeVarMapBox[0] =
        updateTypeVarMap(env, $typeVarMapBox[0], t, index, propPath, [value]);
      if (isEmpty($typeVarMapBox[0][t.name].types)) {
        throw typeVarConstraintViolation(
          env,
          name,
          constraints,
          expTypes,
          index,
          propPath,
          $typeVarMapBox[0][t.name].valuesByPath
        );
      }
    } else if (!test(env, t, value)) {
      throw invalidValue(
        env, name, constraints, expTypes, index, propPath, value
      );
    }
  };

  //  wrapFunction :: ... -> Function
  var wrapFunction = function(
    env,                // :: Array Type
    name,               // :: String
    constraints,        // :: StrMap (Array TypeClass)
    expTypes,           // :: Array Type
    $typeVarMapBox,     // :: Box TypeVarMap
    index,              // :: Integer
    f                   // :: Function
  ) {
    return function() {
      var args = Array.prototype.slice.call(arguments, 0);
      var expType = expTypes[index];
      var numArgsExpected = expType.keys.length - 1;
      if (args.length !== numArgsExpected) {
        throw invalidArgumentsLength_(env,
                                      name,
                                      constraints,
                                      expTypes,
                                      index,
                                      numArgsExpected,
                                      args);
      }
      var checkValue$ = function(propPath, t, x) {
        checkValue(env,
                   name,
                   constraints,
                   expTypes,
                   $typeVarMapBox,
                   index,
                   propPath,
                   t,
                   x);
      };
      expType.keys.slice(0, -1).forEach(function(k, idx) {
        checkValue$([k], expType.types[k].type, args[idx]);
      });

      var output = f.apply(this, arguments);
      var k = last(expType.keys);
      checkValue$([k], expType.types[k].type, output);
      return output;
    };
  };

  //  wrapFunctions :: ... -> Array Any
  var wrapFunctions = function(
    env,                // :: Array Type
    name,               // :: String
    constraints,        // :: StrMap (Array TypeClass)
    expTypes,           // :: Array Type
    $typeVarMapBox,     // :: Box TypeVarMap
    values              // :: Array Any
  ) {
    return values.map(function(value, idx) {
      return expTypes[idx].type === FUNCTION ?
        wrapFunction(env,
                     name,
                     constraints,
                     expTypes,
                     $typeVarMapBox,
                     idx,
                     value) :
        value;
    });
  };

  //  invalidArgumentsLength :: (String, Integer, Integer) -> Error
  var invalidArgumentsLength = function(name, expectedLength, actualLength) {
    return new TypeError(q(name) +
                         ' requires ' + numArgs(expectedLength) + ';' +
                         ' received ' + numArgs(actualLength));
  };

  //  constraintsRepr :: ... -> String
  var constraintsRepr = function(
    constraints,    // :: StrMap (Array TypeClass)
    outer,          // :: String -> String
    inner           // :: String -> TypeClass -> String -> String
  ) {
    var $reprs = [];
    Object.keys(constraints).sort().forEach(function(k) {
      var f = inner(k);
      constraints[k].forEach(function(typeClass) {
        $reprs.push(f(typeClass)(stripNamespace(typeClass.name) + ' ' + k));
      });
    });
    return when($reprs.length > 0,
                function(s) { return s + outer(' => '); },
                when($reprs.length > 1,
                     wrap(outer('('))(outer(')')),
                     $reprs.join(outer(', '))));
  };

  //  label :: String -> String -> String
  var label = function(label) {
    return function(s) {
      var delta = s.length - label.length;
      return strRepeat(' ', Math.floor(delta / 2)) + label +
             strRepeat(' ', Math.ceil(delta / 2));
    };
  };

  //  showType :: Type -> String
  var showType = function(t) {
    return unless(t.type === FUNCTION || t.type === RECORD || isEmpty(t.keys),
                  stripOutermostParens,
                  String(t));
  };

  //  showTypeQuoted :: Type -> String
  var showTypeQuoted = function(t) {
    return q(unless(t.type === RECORD || isEmpty(t.keys),
                    stripOutermostParens,
                    String(t)));
  };

  //  showValuesAndTypes :: (Array Type, Array Any, Integer) -> String
  var showValuesAndTypes = function(env, values, pos) {
    return String(pos) + ')  ' + Z.map(function(x) {
      var types = determineActualTypesLoose(env, env, [x]);
      return Z.toString(x) + ' :: ' + Z.map(showType, types).join(', ');
    }, values).join('\n    ');
  };

  //  _underline :: ... -> String
  var _underline = function recur(
    t,              // :: Type
    propPath,       // :: PropPath
    formatType3     // :: Type -> Array String -> String -> String
  ) {
    return unless(t.type === RECORD ||
                    isEmpty(t.keys) ||
                    t.type === FUNCTION && isEmpty(propPath) ||
                    !isEmpty(propPath),
                  stripOutermostParens,
                  formatType3(t)(propPath)(t.format(_, function(k) {
                    return K(recur(t.types[k].type,
                                   Z.concat(propPath, [k]),
                                   formatType3));
                  })));
  };

  //  underline :: ... -> String
  var underline = function(
    name,                   // :: String
    constraints,            // :: StrMap (Array TypeClass)
    expTypes,               // :: Array Type
    underlineConstraint,    // :: String -> TypeClass -> String -> String
    formatType5             // :: Integer -> (String -> String) -> Type ->
                            //      PropPath -> String -> String
  ) {
    var st = expTypes.reduce(function(st, t, index) {
      var formatType4 = formatType5(index);
      var counter = st.counter;
      var replace = function(s) { return label(String(counter += 1))(s); };
      return {
        carets: Z.concat(st.carets, [_underline(t, [], formatType4(r('^')))]),
        numbers: Z.concat(st.numbers,
                          [_underline(t, [], formatType4(replace))]),
        counter: counter
      };
    }, {carets: [], numbers: [], counter: 0});

    return name + ' :: ' +
             constraintsRepr(constraints, id, K(K(id))) +
             Z.map(showType, expTypes).join(' -> ') + '\n' +
           _(name + ' :: ') +
             constraintsRepr(constraints, _, underlineConstraint) +
             st.carets.join(_(' -> ')) + '\n' +
           _(name + ' :: ') +
             constraintsRepr(constraints, _, K(K(_))) +
             st.numbers.join(_(' -> ')) + '\n';
  };

  //  resolvePropPath :: (Type, Array String) -> Type
  var resolvePropPath = function(t, propPath) {
    return Z.reduce(function(t, prop) { return t.types[prop].type; },
                    t,
                    propPath);
  };

  //  formatType6 ::
  //    PropPath -> Integer -> (String -> String) ->
  //      Type -> PropPath -> String -> String
  var formatType6 = function(indexedPropPath) {
    return function(index_) {
      return function(f) {
        return function(t) {
          return function(propPath_) {
            var indexedPropPath_ = Z.concat([index_], propPath_);
            var p = isPrefix(indexedPropPath_)(indexedPropPath);
            var q = isPrefix(indexedPropPath)(indexedPropPath_);
            return p && q ? f : p ? id : _;
          };
        };
      };
    };
  };

  //  typeClassConstraintViolation :: ... -> Error
  var typeClassConstraintViolation = function(
    env,            // :: Array Type
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    typeClass,      // :: TypeClass
    index,          // :: Integer
    propPath,       // :: PropPath
    value,          // :: Any
    typeVarMap      // :: TypeVarMap
  ) {
    var expType = resolvePropPath(expTypes[index], propPath);
    return new TypeError(trimTrailingSpaces(
      'Type-class constraint violation\n\n' +
      underline(name,
                constraints,
                expTypes,
                function(tvn) {
                  return function(tc) {
                    return tvn === expType.name && tc.name === typeClass.name ?
                      r('^') :
                      _;
                  };
                },
                formatType6(Z.concat([index], propPath))) +
      '\n' +
      showValuesAndTypes(env, [value], 1) + '\n\n' +
      q(name) + ' requires ' + q(expType.name) + ' to satisfy the ' +
      stripNamespace(typeClass.name) + ' type-class constraint; ' +
      'the value at position 1 does not.\n'
    ));
  };

  //  typeVarConstraintViolation :: ... -> Error
  var typeVarConstraintViolation = function(
    env,            // :: Array Type
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    index,          // :: Integer
    propPath,       // :: PropPath
    valuesByPath    // :: StrMap (Array Any)
  ) {
    //  If we apply an ‘a -> a -> a -> a’ function to Left('x'), Right(1), and
    //  Right(null) we'd like to avoid underlining the first argument position,
    //  since Left('x') is compatible with the other ‘a’ values.
    var key = JSON.stringify(Z.concat([index], propPath));
    var values = valuesByPath[key];

    //  Note: Sorting these keys lexicographically is not "correct", but it
    //  does the right thing for indexes less than 10.
    var keys = Object.keys(valuesByPath).sort().filter(function(k) {
      var values_ = valuesByPath[k];
      return (
        //  Keep X, the position at which the violation was observed.
        k === key ||
        //  Keep positions whose values are incompatible with the values at X.
        isEmpty(determineActualTypesStrict(env,
                                           env,
                                           Z.concat(values, values_)))
      );
    });

    return new TypeError(trimTrailingSpaces(
      'Type-variable constraint violation\n\n' +
      underlineTypeVars(name,
                        constraints,
                        expTypes,
                        Z.reduce(function($valuesByPath, k) {
                          $valuesByPath[k] = valuesByPath[k];
                          return $valuesByPath;
                        }, {}, keys)) +
      Z.reduce(function(st, k) {
        var values = valuesByPath[k];
        return isEmpty(values) ? st : {
          idx: st.idx + 1,
          s: st.s + '\n' + showValuesAndTypes(env, values, st.idx + 1) + '\n'
        };
      }, {idx: 0, s: ''}, keys).s + '\n' +
      'Since there is no type of which all the above values are ' +
      'members, the type-variable constraint has been violated.\n'
    ));
  };

  //  invalidValue :: ... -> Error
  var invalidValue = function(
    env,            // :: Array Type
    name,           // :: String
    constraints,    // :: StrMap (Array TypeClass)
    expTypes,       // :: Array Type
    index,          // :: Integer
    propPath,       // :: PropPath
    value           // :: Any
  ) {
    return new TypeError(trimTrailingSpaces(
      'Invalid value\n\n' +
      underline(name,
                constraints,
                expTypes,
                K(K(_)),
                formatType6(Z.concat([index], propPath))) +
      '\n' +
      showValuesAndTypes(env, [value], 1) + '\n\n' +
      'The value at position 1 is not a member of ' +
      showTypeQuoted(resolvePropPath(expTypes[index], propPath)) + '.\n'
    ));
  };

  //  invalidArgumentsLength_ :: ... -> Error
  var invalidArgumentsLength_ = function(
    env,                // :: Array Type
    name,               // :: String
    constraints,        // :: StrMap (Array TypeClass)
    expTypes,           // :: Array Type
    index,              // :: Integer
    numArgsExpected,    // :: Integer
    args                // :: Array Any
  ) {
    return new TypeError(trimTrailingSpaces(
      q(name) + ' applied ' + showTypeQuoted(expTypes[index]) +
      ' to the wrong number of arguments\n\n' +
      underline(
        name,
        constraints,
        expTypes,
        K(K(_)),
        function(index_) {
          return function(f) {
            return function(t) {
              return function(propPath) {
                return function(s) {
                  return index_ === index ?
                    String(t).replace(
                      /^[(](.*) -> (.*)[)]$/,
                      function(s, $1, $2) {
                        return _('(') + f($1) + _(' -> ' + $2 + ')');
                      }
                    ) :
                    _(s);
                };
              };
            };
          };
        }
      ) + '\n' +
      'Expected ' + numArgs(numArgsExpected) +
      ' but received ' + numArgs(args.length) +
      (args.length === 0 ?
         '.\n' :
         Z.reduce(function(s, x) { return s + '  - ' + Z.toString(x) + '\n'; },
                  ':\n\n',
                  args))
    ));
  };

  //  assertRight :: Either a b -> Undefined !
  var assertRight = function(either) {
    if (either.isLeft) throw either.value;
  };

  //  Options :: Type
  var Options = RecordType({checkTypes: $.Boolean, env: $.Array($.Any)});

  //  create :: Options -> Function
  $.create = function(opts) {
    assertRight(satisfactoryTypes(defaultEnv,
                                  'create',
                                  {},
                                  [Options, AnyFunction],
                                  {},
                                  opts,
                                  0));

    //  checkTypes :: Boolean
    var checkTypes = opts.checkTypes;

    //  env :: Array Type
    var env = applyParameterizedTypes(opts.env);

    //  curry :: ... -> Function
    var curry = function(
      name,         // :: String
      constraints,  // :: StrMap (Array TypeClass)
      expTypes,     // :: Array Type
      _typeVarMap,  // :: TypeVarMap
      _values,      // :: Array Any
      _indexes,     // :: Array Integer
      impl          // :: Function
    ) {
      return arity(_indexes.length, function() {
        if (checkTypes) {
          var delta = _indexes.length - arguments.length;
          if (delta < 0) {
            throw invalidArgumentsLength(name,
                                         expTypes.length - 1,
                                         expTypes.length - 1 - delta);
          }
        }
        var typeVarMap = _typeVarMap;
        var values = _values.slice(0);
        var indexes = [];
        for (var idx = 0; idx < _indexes.length; idx += 1) {
          var index = _indexes[idx];

          if (idx < arguments.length &&
              !(typeof arguments[idx] === 'object' &&
                arguments[idx] != null &&
                arguments[idx]['@@functional/placeholder'] === true)) {

            var value = arguments[idx];
            if (checkTypes) {
              var result = satisfactoryTypes(env,
                                             name,
                                             constraints,
                                             expTypes,
                                             typeVarMap,
                                             value,
                                             index);
              assertRight(result);
              typeVarMap = result.value.typeVarMap;
            }
            values[index] = value;
          } else {
            indexes.push(index);
          }
        }
        if (isEmpty(indexes)) {
          if (checkTypes) {
            var returnValue = impl.apply(this,
                                         wrapFunctions(env,
                                                       name,
                                                       constraints,
                                                       expTypes,
                                                       [typeVarMap],
                                                       values));
            assertRight(satisfactoryTypes(env,
                                          name,
                                          constraints,
                                          expTypes,
                                          typeVarMap,
                                          returnValue,
                                          expTypes.length - 1));
            return returnValue;
          } else {
            return impl.apply(this, values);
          }
        } else {
          return curry(name,
                       constraints,
                       expTypes,
                       typeVarMap,
                       values,
                       indexes,
                       impl);
        }
      });
    };

    return function def(name, constraints, expTypes, impl) {
      if (checkTypes) {
        if (arguments.length !== def.length) {
          throw invalidArgumentsLength('def', def.length, arguments.length);
        }

        var types = [$.String,
                     StrMap($.Array(TypeClass)),
                     $.Array(Type),
                     AnyFunction,
                     AnyFunction];
        for (var idx = 0; idx < arguments.length; idx += 1) {
          var arg = arguments[idx];
          assertRight(
            satisfactoryTypes(defaultEnv, 'def', {}, types, {}, arg, idx)
          );
        }
      }

      var values = new Array(expTypes.length - 1);
      if (values.length > 9) {
        throw new RangeError(q('def') + ' cannot define a function ' +
                             'with arity greater than nine');
      }

      return curry(name,
                   constraints,
                   expTypes,
                   {},
                   values,
                   range(0, values.length),
                   impl);
    };
  };

  return $;

}));
