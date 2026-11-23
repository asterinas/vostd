use indexmap::IndexMap;

use crate::commands;
use std::{
    collections::{HashMap, HashSet},
    process::Command,
};

pub fn cargo_tree(package: &str) -> String {
    let mut cmd = Command::new("cargo");
    cmd.arg("tree")
        .args(["--prefix", "depth"])
        .args(["--format", " {p}"])
        .args(["--package", package]);

    commands::run_capture(&mut cmd).stdout
}

#[derive(Debug, Clone)]
pub struct CargoNode {
    pub name: String,
    pub depth: usize,
    pub version: Option<String>,
    pub info: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct CargoTree {
    pub root: Option<CargoNode>,
    pub adj: HashMap<String, Vec<String>>,
    pub details: HashMap<String, CargoNode>,
}

impl CargoTree {
    pub fn parse(tree: &str) -> Self {
        let mut graph = CargoTree::default();
        let mut stack: Vec<String> = Vec::new();
        let pkg_regex = regex::Regex::new(
            r"(?P<depth>\d+)\s+(?P<name>[^\s]+)\s+(?P<version>[^\s]+)\s*(?P<info>.*)?",
        )
        .unwrap();
        for line in tree.lines() {
            let line = pkg_regex.captures(line.trim());
            if line.is_none() {
                warn!("Unable to parse line {:?}", line);
                continue;
            }
            let line = line.unwrap();
            let depth: usize = line.name("depth").unwrap().as_str().parse().unwrap();
            let name = line.name("name").unwrap().as_str().replace("-", "_");
            let version = line.name("version").map(|m| m.as_str());
            let info = line.name("info").map(|m| m.as_str());
            let node = CargoNode {
                name,
                depth,
                version: version.map(|v| v.to_string()),
                info: info.map(|i| i.to_string()),
            };

            match depth {
                0 => {
                    graph.root = Some(node.clone());
                }
                _ => {
                    if let Some(parent) = stack.get(depth - 1) {
                        graph
                            .adj
                            .entry(parent.clone())
                            .or_default()
                            .push(node.name.clone());
                    }
                }
            }
            graph.adj.entry(node.name.clone()).or_default();
            if stack.len() > depth {
                stack.truncate(depth);
            }
            stack.push(node.name.clone());
            graph.details.insert(node.name.clone(), node);
        }

        graph
    }

    pub fn topology_sort(&self) -> Vec<String> {
        let mut visited = HashSet::new();
        let mut order: Vec<String> = Vec::new();

        fn dfs(
            node: &str,
            graph: &HashMap<String, Vec<String>>,
            visited: &mut HashSet<String>,
            order: &mut Vec<String>,
        ) {
            if !visited.insert(node.to_string()) {
                return;
            }
            if let Some(children) = graph.get(node) {
                for c in children {
                    dfs(c, graph, visited, order);
                }
            }
            order.push(node.to_string());
        }

        if let Some(root) = &self.root {
            dfs(&root.name, &self.adj, &mut visited, &mut order);
        } else {
            for node in self.adj.keys() {
                dfs(node, &self.adj, &mut visited, &mut order);
            }
        }

        order
    }

    pub fn rank(&self) -> HashMap<String, usize> {
        let mut rank = HashMap::new();
        let order = self.topology_sort();
        for (i, node) in order.iter().enumerate() {
            rank.insert(node.clone(), i);
        }
        rank
    }

    pub fn reorder<T>(&self, crates: &mut IndexMap<String, T>) {
        let r = self.rank();
        crates.sort_by(|a, _, b, _| {
            let a = r.get(a).unwrap_or(&usize::MAX);
            let b = r.get(b).unwrap_or(&usize::MAX);
            a.cmp(b)
        });
    }
}
