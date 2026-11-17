"""Strict typed JSON and canonical identities, without third-party dependencies."""

from dataclasses import MISSING, fields, is_dataclass
import hashlib
import json
from typing import Literal, Union, get_args, get_origin, get_type_hints


class ValidationError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ValidationError(message)


def decode(cls, value, path="$", *, validate=True):
    origin, args = get_origin(cls), get_args(cls)
    if origin is Union:
        errors = []
        for alternative in args:
            try:
                return decode(alternative, value, path, validate=validate)
            except ValidationError as error:
                errors.append(str(error))
        raise ValidationError(f"{path}: no matching alternative: {'; '.join(errors)}")
    if origin is Literal:
        require(any(type(value) is type(a) and value == a for a in args),
                f"{path}: expected one of {args!r}")
        return value
    if origin is list:
        require(type(value) is list, f"{path}: expected array")
        return [decode(args[0], item, f"{path}[{i}]", validate=validate)
                for i, item in enumerate(value)]
    if is_dataclass(cls):
        require(type(value) is dict, f"{path}: expected object")
        names = {f.name for f in fields(cls)}
        require(not value.keys() - names,
                f"{path}: unknown fields {sorted(value.keys() - names)}")
        hints = get_type_hints(cls)
        kwargs = {}
        for field in fields(cls):
            if field.name in value:
                kwargs[field.name] = decode(hints[field.name], value[field.name],
                                           f"{path}.{field.name}", validate=validate)
            else:
                require(field.default is not MISSING or field.default_factory is not MISSING,
                        f"{path}.{field.name}: required field")
        result = cls(**kwargs)
        if validate and hasattr(result, "validate"):
            try:
                result.validate()
            except ValidationError as error:
                raise ValidationError(f"{path}: {error}") from error
        return result
    require(type(value) is cls, f"{path}: expected {cls.__name__}")
    if cls is int:
        require(0 <= value < 2**64, f"{path}: integer outside uint64 range")
    if cls is str:
        require(bool(value), f"{path}: empty string")
    return value


def plain(value):
    if is_dataclass(value):
        return {f.name: plain(getattr(value, f.name)) for f in fields(value)}
    if isinstance(value, (list, tuple)):
        return [plain(item) for item in value]
    if isinstance(value, dict):
        return {key: plain(item) for key, item in value.items()}
    return value


def canonical(value):
    # v1 uses only uint64 integers, booleans, strings, null, lists and objects.
    # No floats, locale-sensitive formatting, NaN, or implicit unit conversions.
    return json.dumps(plain(value), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=False).encode("ascii")


def identity(kind, value):
    return kind + "-" + hashlib.sha256(canonical(value)).hexdigest()


def _object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON field: {key}")
        result[key] = value
    return result


def load_json(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream, object_pairs_hook=_object,
                         parse_constant=lambda value: (_ for _ in ()).throw(
                             ValidationError(f"non-finite JSON number: {value}")))


def json_schema(cls):
    """Publish structural schemas; cross-field constraints also use decode()."""
    definitions = {}

    def schema(t):
        origin, args = get_origin(t), get_args(t)
        if origin is Union:
            return {"anyOf": [schema(a) for a in args]}
        if origin is Literal:
            return {"enum": list(args)}
        if origin is list:
            return {"type": "array", "items": schema(args[0])}
        if is_dataclass(t):
            name = t.__name__
            if name not in definitions:
                definitions[name] = {}
                hints = get_type_hints(t)
                definitions[name] = {
                    "type": "object", "additionalProperties": False,
                    "properties": {f.name: schema(hints[f.name]) for f in fields(t)},
                    "required": [f.name for f in fields(t)
                                 if f.default is MISSING and f.default_factory is MISSING],
                }
            return {"$ref": f"#/$defs/{name}"}
        # A real is a JSON number spelled with a fraction or exponent (decode
        # tells it from an integer by its parsed type); non-finite ones are
        # refused at parse time.
        return {int: {"type": "integer", "minimum": 0, "maximum": 2**64 - 1},
                float: {"type": "number"},
                bool: {"type": "boolean"}, str: {"type": "string", "minLength": 1},
                type(None): {"type": "null"}}[t]

    root = schema(cls)
    return {"$schema": "https://json-schema.org/draft/2020-12/schema",
            **root, "$defs": definitions}
