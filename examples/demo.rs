//! Basic order-book usage of `Glass`.
//!
//! Run with: `cargo run --example demo`

use glass_rs::Glass;

fn main() {
    let mut book = Glass::new();

    // Insert price levels (price -> quantity).
    book.insert(100, 500);
    book.insert(110, 300);
    book.insert(90, 400);
    println!("book: {book:?}");

    // Point lookups.
    println!("get(100) = {:?}", book.get(100)); // Some(500)
    println!("min = {:?}, max = {:?}", book.min(), book.max());

    // Adjust a level in place; reaching zero deletes the level.
    book.update_value(110, |q| *q += 200);
    println!("get(110) after +200 = {:?}", book.get(110)); // Some(500)

    // Iterate the book from the best price up.
    for (price, qty) in &book {
        println!("level {price} x {qty}");
    }

    // BTreeMap-style navigation.
    println!("next after 90: {:?}", book.next_level(90)); // Some((100, 500))
    println!(
        "levels in 95..=110: {:?}",
        book.range(95..=110).collect::<Vec<_>>()
    );

    // Estimate, then execute a market buy of 700 shares (cheapest first).
    let estimate = book.compute_buy_cost(700);
    let cost = book.buy_shares(700);
    assert_eq!(estimate, cost);
    println!("bought 700 shares for {cost}"); // 90*400 + 100*300 = 66000

    // Sell into the book (highest levels first).
    let proceeds = book.sell_shares(100);
    println!("sold 100 shares for {proceeds}");

    println!("remaining: {:?}", book.iter().collect::<Vec<_>>());
}
