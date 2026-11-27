//! `modules.renamer.PoolInterceptor`: the old and new names of renamed
//! classes and members, consulted while classes are loaded again.

use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub struct PoolInterceptor {
    map_old_to_new_names: FxHashMap<String, String>,
    map_new_to_old_names: FxHashMap<String, String>,
}

impl PoolInterceptor {
    pub fn add_name(&mut self, old_name: &str, new_name: &str) {
        self.map_old_to_new_names
            .insert(old_name.to_owned(), new_name.to_owned());
        self.map_new_to_old_names
            .insert(new_name.to_owned(), old_name.to_owned());
    }

    pub fn get_name(&self, old_name: &str) -> Option<&str> {
        self.map_old_to_new_names.get(old_name).map(String::as_str)
    }

    pub fn get_old_name(&self, new_name: &str) -> Option<&str> {
        self.map_new_to_old_names.get(new_name).map(String::as_str)
    }
}
