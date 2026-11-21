//! Embedded Alloy standard library (`open util/ordering` etc.).
//! Copied verbatim from org.alloytools.alloy.core/src/main/resources/models/util.
//! Java resolves `open util/X` to these files when no `util/X.als` exists next to the model.
//! Also copied verbatim from the distribution's `models/` resources: the `examples/algorithms/messaging`
//! model that the corpus opens (from org.alloytools.alloy.extra/extra/models).

pub fn lookup(name: &str) -> Option<&'static str> {
    Some(match name {
        "util/boolean" => include_str!("../lib/util/boolean.als"),
        "util/graph" => include_str!("../lib/util/graph.als"),
        "util/integer" => include_str!("../lib/util/integer.als"),
        "util/natural" => include_str!("../lib/util/natural.als"),
        "util/ordering" => include_str!("../lib/util/ordering.als"),
        "util/relation" => include_str!("../lib/util/relation.als"),
        "util/seqrel" => include_str!("../lib/util/seqrel.als"),
        "util/sequence" => include_str!("../lib/util/sequence.als"),
        "util/sequniv" => include_str!("../lib/util/sequniv.als"),
        "util/ternary" => include_str!("../lib/util/ternary.als"),
        "util/time" => include_str!("../lib/util/time.als"),
        "examples/algorithms/messaging" => include_str!("../lib/examples/algorithms/messaging.als"),
        _ => return None,
    })
}
