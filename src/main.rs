use glass_rs::Glass;

fn main() {
    let mut glass = Glass::new();

    // Insert (u32 key, u64 value)
    glass.insert(123u32, 999999999999u64);
    glass.insert(456u32, 888888888888u64);

    // Get
    if let Some(val) = glass.get(123u32) {
        println!("Found: {val}"); // Found: 999999999999
    }

    // Remove
    let removed = glass.remove(123u32);
    println!("Removed: {removed:?}"); // Some(999999999999)
    println!("Get after remove: {:?}", glass.get(123u32)); // None

    if let Some(val) = glass.get(456u32) {
        println!("Found: {val}"); // Found: 999999999999
    }

    // Min and max
    if let Some((min_key, min_val)) = glass.min() {
        println!("Min: {min_key} -> {min_val}"); // Min: 123 -> 999999999999 (assuming it's the smallest)
    }

    if let Some((max_key, max_val)) = glass.max() {
        println!("Max: {max_key} -> {max_val}"); // Min: 123 -> 999999999999 (assuming it's the smallest)
    }

    let mut glass = Glass::new();

    // Insert some keys (assume values are small for sum to make sense)
    glass.insert(10u32, 500u64);
    glass.insert(20u32, 600u64);
    glass.insert(30u32, 700u64);
    glass.insert(40u32, 800u64);

    let cost = glass.compute_buy_cost(1000);
    println!("cost: {cost}");
    let cost = glass.buy_shares(200);
    println!("cost: {cost}");
}
