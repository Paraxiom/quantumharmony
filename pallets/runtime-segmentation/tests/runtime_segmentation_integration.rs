//! Integration tests for Runtime Segmentation
//!
//! Tests the 512-segment toroidal mesh topology at the workspace level.
//! Run with: cargo test --test runtime_segmentation_integration

use pallet_runtime_segmentation::{
    coordinates_to_id, id_to_coordinates, get_adjacent_segments, toroidal_distance,
    SegmentCoordinates, MESH_SIZE_X, MESH_SIZE_Y, MESH_SIZE_Z, TOTAL_SEGMENTS,
};

#[test]
fn test_all_512_segments_have_valid_ids() {
    // Verify all 512 segments can be converted to/from coordinates
    for id in 0..TOTAL_SEGMENTS as u32 {
        let coords = id_to_coordinates(id);
        let back_to_id = coordinates_to_id(&coords);
        assert_eq!(id, back_to_id, "Round-trip conversion failed for segment {}", id);

        // Verify coordinates are within bounds
        assert!(coords.x < MESH_SIZE_X as u8, "X coordinate out of bounds for segment {}", id);
        assert!(coords.y < MESH_SIZE_Y as u8, "Y coordinate out of bounds for segment {}", id);
        assert!(coords.z < MESH_SIZE_Z as u8, "Z coordinate out of bounds for segment {}", id);
    }
}

#[test]
fn test_all_segments_have_exactly_6_neighbors() {
    // Every segment in a 3D torus should have exactly 6 neighbors
    for id in 0..TOTAL_SEGMENTS as u32 {
        let coords = id_to_coordinates(id);
        let neighbors = get_adjacent_segments(&coords);
        assert_eq!(
            neighbors.len(),
            6,
            "Segment {} at {:?} should have 6 neighbors, got {}",
            id, coords, neighbors.len()
        );

        // Verify all neighbors are valid
        for neighbor in &neighbors {
            let neighbor_id = coordinates_to_id(neighbor);
            assert!(
                neighbor_id < TOTAL_SEGMENTS as u32,
                "Neighbor ID {} is out of range for segment {}",
                neighbor_id, id
            );
        }
    }
}

#[test]
fn test_toroidal_wraparound_at_edges() {
    // Test X-axis wraparound
    let origin = SegmentCoordinates { x: 0, y: 4, z: 4 };
    let neighbors = get_adjacent_segments(&origin);
    assert!(
        neighbors.contains(&SegmentCoordinates { x: 7, y: 4, z: 4 }),
        "X-axis should wrap from 0 to 7"
    );
    assert!(
        neighbors.contains(&SegmentCoordinates { x: 1, y: 4, z: 4 }),
        "X-axis should increment from 0 to 1"
    );

    // Test Y-axis wraparound
    let origin = SegmentCoordinates { x: 4, y: 0, z: 4 };
    let neighbors = get_adjacent_segments(&origin);
    assert!(
        neighbors.contains(&SegmentCoordinates { x: 4, y: 7, z: 4 }),
        "Y-axis should wrap from 0 to 7"
    );

    // Test Z-axis wraparound
    let origin = SegmentCoordinates { x: 4, y: 4, z: 0 };
    let neighbors = get_adjacent_segments(&origin);
    assert!(
        neighbors.contains(&SegmentCoordinates { x: 4, y: 4, z: 7 }),
        "Z-axis should wrap from 0 to 7"
    );
}

#[test]
fn test_corner_segments_connectivity() {
    // Test all 8 corners of the cube
    let corners = vec![
        SegmentCoordinates { x: 0, y: 0, z: 0 },
        SegmentCoordinates { x: 7, y: 0, z: 0 },
        SegmentCoordinates { x: 0, y: 7, z: 0 },
        SegmentCoordinates { x: 7, y: 7, z: 0 },
        SegmentCoordinates { x: 0, y: 0, z: 7 },
        SegmentCoordinates { x: 7, y: 0, z: 7 },
        SegmentCoordinates { x: 0, y: 7, z: 7 },
        SegmentCoordinates { x: 7, y: 7, z: 7 },
    ];

    for corner in corners {
        let neighbors = get_adjacent_segments(&corner);
        assert_eq!(
            neighbors.len(),
            6,
            "Corner {:?} should have 6 neighbors due to toroidal wrap",
            corner
        );

        // Verify no neighbor is the corner itself
        for neighbor in &neighbors {
            assert_ne!(
                *neighbor, corner,
                "Corner {:?} listed itself as a neighbor",
                corner
            );
        }
    }
}

#[test]
fn test_toroidal_distance_symmetry() {
    // Distance should be symmetric: d(a,b) == d(b,a)
    let test_cases = vec![
        (SegmentCoordinates { x: 0, y: 0, z: 0 }, SegmentCoordinates { x: 1, y: 0, z: 0 }),
        (SegmentCoordinates { x: 0, y: 0, z: 0 }, SegmentCoordinates { x: 7, y: 0, z: 0 }),
        (SegmentCoordinates { x: 3, y: 3, z: 3 }, SegmentCoordinates { x: 5, y: 5, z: 5 }),
        (SegmentCoordinates { x: 0, y: 4, z: 2 }, SegmentCoordinates { x: 7, y: 3, z: 6 }),
    ];

    for (a, b) in test_cases {
        let dist_ab = toroidal_distance(&a, &b);
        let dist_ba = toroidal_distance(&b, &a);
        assert_eq!(
            dist_ab, dist_ba,
            "Distance should be symmetric: d({:?},{:?}) = {} != {} = d({:?},{:?})",
            a, b, dist_ab, dist_ba, b, a
        );
    }
}

#[test]
fn test_toroidal_distance_shortest_path() {
    // Distance 0->7 should be 1 (wraps around) not 7
    let a = SegmentCoordinates { x: 0, y: 0, z: 0 };
    let b = SegmentCoordinates { x: 7, y: 0, z: 0 };
    let dist = toroidal_distance(&a, &b);
    assert_eq!(dist, 1, "Distance 0->7 should wrap to 1, got {}", dist);

    // Distance 0->4 should be 4 (no wrap)
    let a = SegmentCoordinates { x: 0, y: 0, z: 0 };
    let b = SegmentCoordinates { x: 4, y: 0, z: 0 };
    let dist = toroidal_distance(&a, &b);
    assert_eq!(dist, 16, "Distance 0->4 should be 4^2=16, got {}", dist);
}

#[test]
fn test_segment_id_boundaries() {
    // Test first segment
    assert_eq!(coordinates_to_id(&SegmentCoordinates { x: 0, y: 0, z: 0 }), 0);

    // Test last segment
    assert_eq!(coordinates_to_id(&SegmentCoordinates { x: 7, y: 7, z: 7 }), 511);

    // Test middle segments
    assert_eq!(coordinates_to_id(&SegmentCoordinates { x: 0, y: 0, z: 4 }), 256);
    assert_eq!(coordinates_to_id(&SegmentCoordinates { x: 4, y: 4, z: 4 }), 292);
}

#[test]
fn test_no_duplicate_neighbors() {
    // Each segment should have unique neighbors
    for id in 0..TOTAL_SEGMENTS as u32 {
        let coords = id_to_coordinates(id);
        let neighbors = get_adjacent_segments(&coords);

        // Check for duplicates
        for i in 0..neighbors.len() {
            for j in (i+1)..neighbors.len() {
                assert_ne!(
                    neighbors[i], neighbors[j],
                    "Segment {} has duplicate neighbor: {:?}",
                    id, neighbors[i]
                );
            }
        }
    }
}

#[test]
fn test_neighbor_reciprocity() {
    // If B is a neighbor of A, then A should be a neighbor of B
    for id in 0..TOTAL_SEGMENTS as u32 {
        let coords_a = id_to_coordinates(id);
        let neighbors_of_a = get_adjacent_segments(&coords_a);

        for neighbor_coords in &neighbors_of_a {
            let neighbors_of_neighbor = get_adjacent_segments(neighbor_coords);
            assert!(
                neighbors_of_neighbor.contains(&coords_a),
                "Segment {:?} has neighbor {:?}, but reciprocal not found",
                coords_a, neighbor_coords
            );
        }
    }
}

#[test]
fn test_mesh_dimensions() {
    assert_eq!(MESH_SIZE_X, 8, "Mesh X dimension should be 8");
    assert_eq!(MESH_SIZE_Y, 8, "Mesh Y dimension should be 8");
    assert_eq!(MESH_SIZE_Z, 8, "Mesh Z dimension should be 8");
    assert_eq!(TOTAL_SEGMENTS, 512, "Total segments should be 512");
    assert_eq!(MESH_SIZE_X * MESH_SIZE_Y * MESH_SIZE_Z, TOTAL_SEGMENTS);
}

#[test]
fn test_segment_distribution() {
    // Verify segments are evenly distributed across all layers
    let mut z_layer_counts = vec![0u32; MESH_SIZE_Z];

    for id in 0..TOTAL_SEGMENTS as u32 {
        let coords = id_to_coordinates(id);
        z_layer_counts[coords.z as usize] += 1;
    }

    // Each Z layer should have exactly 64 segments (8x8)
    for (z, count) in z_layer_counts.iter().enumerate() {
        assert_eq!(
            *count, 64,
            "Z-layer {} should have 64 segments, got {}",
            z, count
        );
    }
}

#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn benchmark_coordinate_conversion() {
        let start = Instant::now();
        let iterations = 100_000;

        for _ in 0..iterations {
            for id in 0..TOTAL_SEGMENTS as u32 {
                let coords = id_to_coordinates(id);
                let _ = coordinates_to_id(&coords);
            }
        }

        let duration = start.elapsed();
        let ops_per_sec = (iterations * TOTAL_SEGMENTS) as f64 / duration.as_secs_f64();

        println!("Coordinate conversions: {:.0} ops/sec", ops_per_sec);
        assert!(ops_per_sec > 1_000_000.0, "Should handle >1M conversions/sec");
    }

    #[test]
    fn benchmark_neighbor_calculation() {
        let start = Instant::now();
        let iterations = 10_000;

        for _ in 0..iterations {
            for id in 0..TOTAL_SEGMENTS as u32 {
                let coords = id_to_coordinates(id);
                let _ = get_adjacent_segments(&coords);
            }
        }

        let duration = start.elapsed();
        let ops_per_sec = (iterations * TOTAL_SEGMENTS) as f64 / duration.as_secs_f64();

        println!("Neighbor calculations: {:.0} ops/sec", ops_per_sec);
        assert!(ops_per_sec > 100_000.0, "Should handle >100K neighbor calcs/sec");
    }
}
