module std::option_spec {
  use std::option;
  use std::option::Option;

  #[spec(prove)]
  fun none_spec<Element>(): Option<Element> {
        let result = option::none<Element>();
        result
  }

  #[spec(prove)]
  fun some_spec<Element>(e: Element): Option<Element> {
        let result = option::some(e);
        result
  }

  #[spec(prove)]
  fun is_none_spec<Element>(t: &Option<Element>): bool {
        let result = option::is_none(t);
        result
  }

  #[spec(prove)]
  fun is_some_spec<Element>(t: &Option<Element>): bool {
        let result = option::is_some(t);
        result
  }

  #[spec(prove)]
  fun contains_spec<Element>(t: &Option<Element>, e_ref: &Element): bool {
        let result = option::contains(t, e_ref);
        result
  }

  #[spec(prove)]
  fun borrow_spec<Element>(t: &Option<Element>): &Element {
        let result = option::borrow(t);
        result
  }

  #[spec(prove)]
  fun borrow_with_default_spec<Element>(t: &Option<Element>, default_ref: &Element): &Element {
        let result = option::borrow_with_default(t, default_ref);
        result
  }

  #[spec(prove)]
  fun get_with_default_spec<Element: copy + drop>(t: &Option<Element>, default: Element): Element {
        let result = option::get_with_default(t, default);
        result
  }

  #[spec(prove)]
  fun fill_spec<Element>(t: &mut Option<Element>, e: Element) {
        option::fill(t, e);
  }

  #[spec(prove)]
  fun extract_spec<Element>(t: &mut Option<Element>): Element {
        let result = option::extract(t);
        result
  }

  #[spec(prove)]
  fun borrow_mut_spec<Element>(t: &mut Option<Element>): &mut Element {
        let result = option::borrow_mut(t);
        result
  }

  #[spec(prove)]
  fun swap_spec<Element>(t: &mut Option<Element>, e: Element): Element {
        let result = option::swap(t, e);
        result
  }

  #[spec(prove)]
  fun swap_or_fill_spec<Element>(t: &mut Option<Element>, e: Element): Option<Element> {
        let result = option::swap_or_fill(t, e);
        result
  }

  #[spec(prove)]
  fun destroy_with_default_spec<Element: drop>(t: Option<Element>, default: Element): Element {
        let result = option::destroy_with_default(t, default);
        result
  }

  #[spec(prove)]
  fun destroy_some_spec<Element>(t: Option<Element>): Element {
        let result = option::destroy_some(t);
        result
  }

  #[spec(prove)]
  fun destroy_none_spec<Element>(t: Option<Element>) {
        option::destroy_none(t);
  }

  #[spec(prove)]
  fun to_vec_spec<Element>(t: Option<Element>): vector<Element> {
        let result = option::to_vec(t);
        result
  }
}
