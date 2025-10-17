package smap

import (
	"fmt"
	"sync"
	"testing"
)

// Note: these tests were generated.

func TestSetAndGet(t *testing.T) {
	m := New[string, int]()

	// Set and get a value
	m.Set("foo", 42)
	val, ok := m.Get("foo")
	if !ok {
		t.Error("Expected key 'foo' to exist")
	}
	if val != 42 {
		t.Errorf("Expected value 42, got %d", val)
	}

	// Get non-existent key
	_, ok = m.Get("bar")
	if ok {
		t.Error("Expected key 'bar' to not exist")
	}

	// Update existing key
	m.Set("foo", 100)
	val, ok = m.Get("foo")
	if !ok || val != 100 {
		t.Errorf("Expected updated value 100, got %d", val)
	}
}

func TestDelete(t *testing.T) {
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)

	// Delete existing key
	m.Delete("foo")
	_, ok := m.Get("foo")
	if ok {
		t.Error("Expected key 'foo' to be deleted")
	}

	// Verify other key still exists
	val, ok := m.Get("bar")
	if !ok || val != 2 {
		t.Error("Expected key 'bar' to still exist")
	}

	// Delete non-existent key (should not panic)
	m.Delete("nonexistent")
}

func TestHas(t *testing.T) {
	m := New[string, int]()

	// Check non-existent key
	if m.Has("foo") {
		t.Error("Expected Has to return false for non-existent key")
	}

	// Set and check
	m.Set("foo", 42)
	if !m.Has("foo") {
		t.Error("Expected Has to return true for existing key")
	}

	// Delete and check
	m.Delete("foo")
	if m.Has("foo") {
		t.Error("Expected Has to return false after delete")
	}
}

func TestLen(t *testing.T) {
	m := New[string, int]()

	// Empty map
	if m.Len() != 0 {
		t.Errorf("Expected length 0, got %d", m.Len())
	}

	// Add items
	m.Set("a", 1)
	if m.Len() != 1 {
		t.Errorf("Expected length 1, got %d", m.Len())
	}

	m.Set("b", 2)
	m.Set("c", 3)
	if m.Len() != 3 {
		t.Errorf("Expected length 3, got %d", m.Len())
	}

	// Update existing (shouldn't change length)
	m.Set("a", 10)
	if m.Len() != 3 {
		t.Errorf("Expected length 3 after update, got %d", m.Len())
	}

	// Delete item
	m.Delete("b")
	if m.Len() != 2 {
		t.Errorf("Expected length 2 after delete, got %d", m.Len())
	}
}

func TestClear(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	m.Set("c", 3)

	// Verify items exist
	if m.Len() != 3 {
		t.Error("Expected 3 items before clear")
	}

	// Clear
	m.Clear()

	// Verify map is empty
	if m.Len() != 0 {
		t.Errorf("Expected length 0 after clear, got %d", m.Len())
	}

	if m.Has("a") || m.Has("b") || m.Has("c") {
		t.Error("Expected all keys to be removed after clear")
	}

	// Clear empty map (should not panic)
	m.Clear()
	if m.Len() != 0 {
		t.Error("Expected length to remain 0")
	}
}

func TestAll(t *testing.T) {
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)
	m.Set("baz", 3)

	// Collect all key-value pairs
	collected := make(map[string]int)
	for k, v := range m.All() {
		collected[k] = v
	}

	// Verify all entries were collected
	if len(collected) != 3 {
		t.Errorf("Expected 3 entries, got %d", len(collected))
	}
	if collected["foo"] != 1 {
		t.Errorf("Expected foo=1, got %d", collected["foo"])
	}
	if collected["bar"] != 2 {
		t.Errorf("Expected bar=2, got %d", collected["bar"])
	}
	if collected["baz"] != 3 {
		t.Errorf("Expected baz=3, got %d", collected["baz"])
	}
}

func TestAllEmpty(t *testing.T) {
	m := New[string, int]()

	count := 0
	for range m.All() {
		count++
	}

	if count != 0 {
		t.Errorf("Expected 0 iterations for empty map, got %d", count)
	}
}

func TestAllEarlyTermination(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	m.Set("c", 3)
	m.Set("d", 4)

	count := 0
	for range m.All() {
		count++
		if count == 2 {
			break
		}
	}

	if count != 2 {
		t.Errorf("Expected early termination at 2 iterations, got %d", count)
	}
}

func TestValues(t *testing.T) {
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)
	m.Set("baz", 3)

	// Collect all values
	values := make(map[int]bool)
	for v := range m.Values() {
		values[v] = true
	}

	// Verify all values were collected
	if len(values) != 3 {
		t.Errorf("Expected 3 values, got %d", len(values))
	}
	if !values[1] || !values[2] || !values[3] {
		t.Errorf("Expected values 1, 2, 3, got %v", values)
	}
}

func TestValuesEmpty(t *testing.T) {
	m := New[string, int]()

	count := 0
	for range m.Values() {
		count++
	}

	if count != 0 {
		t.Errorf("Expected 0 iterations for empty map, got %d", count)
	}
}

func TestValuesEarlyTermination(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	m.Set("c", 3)

	count := 0
	for range m.Values() {
		count++
		if count == 1 {
			break
		}
	}

	if count != 1 {
		t.Errorf("Expected early termination at 1 iteration, got %d", count)
	}
}

func TestKeys(t *testing.T) {
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)
	m.Set("baz", 3)

	// Collect all keys
	keys := make(map[string]bool)
	for k := range m.Keys() {
		keys[k] = true
	}

	// Verify all keys were collected
	if len(keys) != 3 {
		t.Errorf("Expected 3 keys, got %d", len(keys))
	}
	if !keys["foo"] || !keys["bar"] || !keys["baz"] {
		t.Errorf("Expected keys foo, bar, baz, got %v", keys)
	}
}

func TestKeysEmpty(t *testing.T) {
	m := New[string, int]()

	count := 0
	for range m.Keys() {
		count++
	}

	if count != 0 {
		t.Errorf("Expected 0 iterations for empty map, got %d", count)
	}
}

func TestKeysEarlyTermination(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	m.Set("c", 3)
	m.Set("d", 4)
	m.Set("e", 5)

	count := 0
	for range m.Keys() {
		count++
		if count == 3 {
			break
		}
	}

	if count != 3 {
		t.Errorf("Expected early termination at 3 iterations, got %d", count)
	}
}

func TestKeysSorted(t *testing.T) {
	m := New[string, int]()
	m.Set("c", 3)
	m.Set("a", 1)
	m.Set("b", 2)

	expected := []string{"a", "b", "c"}
	idx := 0
	for k := range m.KeysSorted(func(a, b string) bool { return a < b }) {
		if idx >= len(expected) {
			t.Fatalf("received more keys than expected; extra key %q", k)
		}
		if k != expected[idx] {
			t.Fatalf("expected key %q at position %d, got %q", expected[idx], idx, k)
		}
		idx++
	}
	if idx != len(expected) {
		t.Fatalf("expected %d keys, got %d", len(expected), idx)
	}

	t.Run("earlyTermination", func(t *testing.T) {
		seqMap := New[string, int]()
		seqMap.Set("y", 2)
		seqMap.Set("x", 1)
		seq := seqMap.KeysSorted(func(a, b string) bool { return a < b })
		calls := 0
		seq(func(string) bool {
			calls++
			return false
		})
		if calls != 1 {
			t.Fatalf("expected to stop after 1 iteration, got %d", calls)
		}
	})

	t.Run("structKeyCustomSort", func(t *testing.T) {
		type compoundKey struct {
			label    string
			priority int
		}

		s := New[compoundKey, int]()
		s.Set(compoundKey{label: "gamma", priority: 2}, 20)
		s.Set(compoundKey{label: "alpha", priority: 3}, 30)
		s.Set(compoundKey{label: "omega", priority: 1}, 10)

		less := func(a, b compoundKey) bool {
			return a.priority < b.priority
		}

		order := make([]compoundKey, 0, 3)
		for k := range s.KeysSorted(less) {
			order = append(order, k)
		}

		expectedOrder := []compoundKey{
			{label: "omega", priority: 1},
			{label: "gamma", priority: 2},
			{label: "alpha", priority: 3},
		}

		if len(order) != len(expectedOrder) {
			t.Fatalf("expected %d keys, got %d", len(expectedOrder), len(order))
		}

		for i, got := range order {
			want := expectedOrder[i]
			if got != want {
				t.Fatalf("at position %d expected %v, got %v", i, want, got)
			}
		}
	})
}

func TestAllSorted(t *testing.T) {
	m := New[int, string]()
	m.Set(3, "three")
	m.Set(1, "one")
	m.Set(2, "two")

	visited := make([]KV[int, string], 0, 3)
	for k, v := range m.AllSorted(func(a, b int) bool { return a < b }) {
		visited = append(visited, KV[int, string]{Key: k, Value: v})
		if k == 1 {
			m.Delete(2)
		}
	}

	expected := []KV[int, string]{
		{Key: 1, Value: "one"},
		{Key: 3, Value: "three"},
	}

	if len(visited) != len(expected) {
		t.Fatalf("expected %d key/value pairs, got %d", len(expected), len(visited))
	}

	for i, kv := range expected {
		if visited[i] != kv {
			t.Fatalf("expected pair %v at position %d, got %v", kv, i, visited[i])
		}
	}

	t.Run("earlyTermination", func(t *testing.T) {
		seqMap := New[int, string]()
		seqMap.Set(2, "two")
		seqMap.Set(1, "one")
		seq := seqMap.AllSorted(func(a, b int) bool { return a < b })
		calls := 0
		seq(func(int, string) bool {
			calls++
			return false
		})
		if calls != 1 {
			t.Fatalf("expected to stop after 1 iteration, got %d", calls)
		}
	})
}

func TestIteratorWithDifferentTypes(t *testing.T) {
	// Test with different types
	m := New[int, string]()
	m.Set(1, "one")
	m.Set(2, "two")
	m.Set(3, "three")

	// Test All()
	count := 0
	for k, v := range m.All() {
		if k == 1 && v != "one" {
			t.Errorf("Expected key 1 to have value 'one', got '%s'", v)
		}
		count++
	}
	if count != 3 {
		t.Errorf("Expected 3 items, got %d", count)
	}

	// Test Keys()
	keyCount := 0
	for k := range m.Keys() {
		if k < 1 || k > 3 {
			t.Errorf("Unexpected key: %d", k)
		}
		keyCount++
	}
	if keyCount != 3 {
		t.Errorf("Expected 3 keys, got %d", keyCount)
	}

	// Test Values()
	valueCount := 0
	for v := range m.Values() {
		if v != "one" && v != "two" && v != "three" {
			t.Errorf("Unexpected value: %s", v)
		}
		valueCount++
	}
	if valueCount != 3 {
		t.Errorf("Expected 3 values, got %d", valueCount)
	}
}

func TestIteratorAfterModification(t *testing.T) {
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)

	// Iterate and verify
	count := 0
	for range m.All() {
		count++
	}
	if count != 2 {
		t.Errorf("Expected 2 items before modification, got %d", count)
	}

	// Modify map
	m.Set("baz", 3)
	m.Delete("foo")

	// Iterate again and verify changes
	collected := make(map[string]int)
	for k, v := range m.All() {
		collected[k] = v
	}

	if len(collected) != 2 {
		t.Errorf("Expected 2 items after modification, got %d", len(collected))
	}
	if _, exists := collected["foo"]; exists {
		t.Error("Expected 'foo' to be deleted")
	}
	if collected["bar"] != 2 {
		t.Error("Expected 'bar' to still exist with value 2")
	}
	if collected["baz"] != 3 {
		t.Error("Expected 'baz' to exist with value 3")
	}
}

func TestConcurrentReadWrite(t *testing.T) {
	m := New[int, int]()
	const numGoroutines = 100
	const numOperations = 1000

	// Start multiple goroutines performing various operations
	done := make(chan bool, numGoroutines)

	// Writers
	for i := range numGoroutines / 2 {
		go func(id int) {
			for j := range numOperations {
				key := (id * numOperations) + j
				m.Set(key, key*2)
			}
			done <- true
		}(i)
	}

	// Readers
	for i := range numGoroutines / 4 {
		go func(id int) {
			for j := range numOperations {
				key := (id * numOperations) + j
				m.Get(key)
				m.Has(key)
			}
			done <- true
		}(i)
	}

	// Mixed operations (read, write, delete)
	for i := range numGoroutines / 4 {
		go func(id int) {
			for j := range numOperations {
				key := (id * numOperations) + j
				m.Set(key, j)
				m.Get(key)
				if j%2 == 0 {
					m.Delete(key)
				}
				m.Has(key)
			}
			done <- true
		}(i)
	}

	// Wait for all goroutines to complete
	for range numGoroutines {
		<-done
	}

	// Verify map is still functional
	m.Set(999999, 123)
	val, ok := m.Get(999999)
	if !ok || val != 123 {
		t.Error("Map should still be functional after concurrent operations")
	}
}

func TestConcurrentIterators(t *testing.T) {
	m := New[string, int]()
	const numGoroutines = 30
	const numItems = 100

	// Pre-populate the map
	for i := range numItems {
		m.Set(string(rune('A'+i%26))+string(rune('0'+i/26)), i)
	}

	done := make(chan bool, numGoroutines+1)

	// Multiple goroutines iterating with All()
	for range numGoroutines / 3 {
		go func() {
			defer func() { done <- true }()
			count := 0
			for range m.All() {
				count++
			}
			// Just verify iteration completes without panic
		}()
	}

	// Multiple goroutines iterating with Keys()
	for range numGoroutines / 3 {
		go func() {
			defer func() { done <- true }()
			count := 0
			for range m.Keys() {
				count++
			}
		}()
	}

	// Multiple goroutines iterating with Values()
	for range numGoroutines / 3 {
		go func() {
			defer func() { done <- true }()
			count := 0
			for range m.Values() {
				count++
			}
		}()
	}

	// Concurrent writes while iterating
	go func() {
		defer func() { done <- true }()
		for i := range 100 {
			m.Set("concurrent", i)
		}
	}()
	// Wait for all goroutines
	for range numGoroutines + 1 {
		<-done
	}
	// Verify map is still functional after concurrent iterations
	m.Set("test", 999)
	val, ok := m.Get("test")
	if !ok || val != 999 {
		t.Error("Map should still be functional after concurrent iterations")
	}
}

func TestConcurrentClearAndLen(t *testing.T) {
	m := New[int, string]()
	const numGoroutines = 20
	done := make(chan bool, numGoroutines)

	// Goroutines adding items
	for i := range numGoroutines / 2 {
		go func(id int) {
			for j := range 100 {
				m.Set(id*100+j, "value")
			}
			done <- true
		}(i)
	}

	// Goroutines checking length
	for range numGoroutines / 4 {
		go func() {
			for range 100 {
				_ = m.Len()
			}
			done <- true
		}()
	}

	// Goroutines clearing (after a bit)
	for range numGoroutines / 4 {
		go func() {
			for range 10 {
				m.Clear()
			}
			done <- true
		}()
	}

	// Wait for all
	for range numGoroutines {
		<-done
	}

	// Map should still be functional
	m.Clear()
	m.Set(1, "test")
	if m.Len() != 1 {
		t.Errorf("Expected length 1, got %d", m.Len())
	}
}

func TestVersion(t *testing.T) {
	m := New[string, int]()
	initial := m.Version()
	m.Set("a", 1)
	if m.Version() == initial {
		t.Error("Version should increment after Set")
	}
	m.Set("b", 2)
	if m.Version() <= initial+1 {
		t.Error("Version should increment again after another Set")
	}
	m.Delete("a")
	if m.Version() <= initial+2 {
		t.Error("Version should increment after Delete")
	}
}

func TestSetBatch(t *testing.T) {
	m := New[string, int]()
	kvs := []KV[string, int]{
		{"x", 10},
		{"y", 20},
		{"z", 30},
	}
	m.SetBatch(kvs)
	if m.Len() != 3 {
		t.Errorf("Expected 3 entries after SetBatch, got %d", m.Len())
	}
	for _, kv := range kvs {
		v, ok := m.Get(kv.Key)
		if !ok || v != kv.Value {
			t.Errorf("Expected %s=%d, got %d", kv.Key, kv.Value, v)
		}
	}
}

func TestDeleteMultiple(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	m.Set("c", 3)
	m.Delete("a", "b")
	if m.Has("a") || m.Has("b") {
		t.Error("Keys 'a' and 'b' should be deleted")
	}
	if !m.Has("c") {
		t.Error("Key 'c' should still exist")
	}
}

// This deadlocks (by design/as documented) so isn't actually a test.
func DeleteDuringIterationDeadlock(t *testing.T) {
	m := New[string, int]()
	m.Set("a", 1)
	m.Set("b", 2)
	wg := sync.WaitGroup{}
	wg.Add(1)
	go func() {
		for k := range m.Keys() {
			m.Delete(k) // This should deadlock due to lock ordering
		}
		wg.Done()
	}()
	wg.Wait()
	t.Errorf("Unexpected no hang")
}

func TestAllNaturalSort(t *testing.T) { //nolint:gocognit // it's a test!
	t.Run("int", func(t *testing.T) {
		m := New[int, string]()
		m.Set(3, "three")
		m.Set(1, "one")
		m.Set(2, "two")

		expected := []int{1, 2, 3}
		i := 0
		for k, v := range NaturalSort(m) {
			if k != expected[i] {
				t.Errorf("Expected key %d, got %d", expected[i], k)
			}
			if i == 0 && v != "one" {
				t.Errorf("Expected value 'one', got '%s'", v)
			}
			i++
		}
		if i != 3 {
			t.Errorf("Expected 3 iterations, got %d", i)
		}
	})

	t.Run("string", func(t *testing.T) {
		m := New[string, int]()
		m.Set("charlie", 3)
		m.Set("alice", 1)
		m.Set("bob", 2)

		expected := []string{"alice", "bob", "charlie"}
		i := 0
		for k, v := range NaturalSort(m) {
			if k != expected[i] {
				t.Errorf("Expected key %s, got %s", expected[i], k)
			}
			if i == 0 && v != 1 {
				t.Errorf("Expected value 1, got %d", v)
			}
			i++
		}
		if i != 3 {
			t.Errorf("Expected 3 iterations, got %d", i)
		}
	})

	t.Run("keyDeletedDuringIteration", func(t *testing.T) {
		m := New[int, string]()
		m.Set(3, "three")
		m.Set(1, "one")
		m.Set(2, "two")
		m.Set(4, "four")

		visited := make([]KV[int, string], 0, 4)
		for k, v := range NaturalSort(m) {
			visited = append(visited, KV[int, string]{Key: k, Value: v})
			// Delete key 2 after visiting key 1
			if k == 1 {
				m.Delete(2)
			}
		}

		// Expected: 1, 3, 4 (key 2 should be skipped because it was deleted)
		expected := []KV[int, string]{
			{Key: 1, Value: "one"},
			{Key: 3, Value: "three"},
			{Key: 4, Value: "four"},
		}

		if len(visited) != len(expected) {
			t.Fatalf("expected %d key/value pairs, got %d", len(expected), len(visited))
		}

		for i, kv := range expected {
			if visited[i] != kv {
				t.Fatalf("expected pair %v at position %d, got %v", kv, i, visited[i])
			}
		}
	})

	t.Run("earlyTermination", func(t *testing.T) {
		m := New[int, string]()
		m.Set(3, "three")
		m.Set(1, "one")
		m.Set(2, "two")
		m.Set(4, "four")

		calls := 0
		for range NaturalSort(m) {
			calls++
			if calls == 2 {
				break
			}
		}

		if calls != 2 {
			t.Fatalf("expected to stop after 2 iterations, got %d", calls)
		}
	})

	t.Run("earlyTerminationViaYield", func(t *testing.T) {
		m := New[int, string]()
		m.Set(5, "five")
		m.Set(1, "one")
		m.Set(3, "three")

		seq := NaturalSort(m)
		calls := 0
		seq(func(int, string) bool {
			calls++
			return false // Stop immediately
		})

		if calls != 1 {
			t.Fatalf("expected to stop after 1 iteration when yield returns false, got %d", calls)
		}
	})
}

func TestKeysSnapshot(t *testing.T) {
	m := New[string, int]()

	// Test empty map
	keys := m.KeysSnapshot()
	if len(keys) != 0 {
		t.Errorf("Expected empty snapshot, got %d keys", len(keys))
	}

	// Test with data
	m.Set("foo", 1)
	m.Set("bar", 2)
	m.Set("baz", 3)

	keys = m.KeysSnapshot()
	if len(keys) != 3 {
		t.Errorf("Expected 3 keys in snapshot, got %d", len(keys))
	}

	// Verify all keys are present
	keyMap := make(map[string]bool)
	for _, k := range keys {
		keyMap[k] = true
	}
	if !keyMap["foo"] || !keyMap["bar"] || !keyMap["baz"] {
		t.Errorf("Expected all keys to be in snapshot, got %v", keys)
	}

	// Verify snapshot is independent - modifying original map shouldn't affect snapshot
	oldKeys := m.KeysSnapshot()
	m.Set("qux", 4)
	m.Delete("foo")

	if len(oldKeys) != 3 {
		t.Errorf("Snapshot should be independent of map changes, expected 3 keys, got %d", len(oldKeys))
	}
	// Check KeysValuesSnapshot as well
	kvPairs := m.KeysValuesSnapshot()
	if len(kvPairs) != 3 {
		t.Errorf("Expected 3 key-value pairs in snapshot, got %d", len(kvPairs))
	}
	for _, kv := range kvPairs {
		if kv.Key == "foo" {
			t.Errorf("Snapshot should contain old key 'foo', but it was deleted from map")
		}
		mval, ok := m.Get(kv.Key)
		if !ok || mval != kv.Value {
			t.Errorf("Snapshot key-value pair mismatch for key %s: expected %d, got %d", kv.Key, kv.Value, mval)
		}
	}
}

func TestTransfer(t *testing.T) {
	// Create a regular map
	regularMap := map[string]int{
		"foo": 1,
		"bar": 2,
		"baz": 3,
	}

	// Transfer ownership to sync Map
	m := Transfer(regularMap)

	// Verify contents
	if m.Len() != 3 {
		t.Errorf("Expected 3 entries after transfer, got %d", m.Len())
	}

	val, ok := m.Get("foo")
	if !ok || val != 1 {
		t.Errorf("Expected foo=1, got %d (ok=%v)", val, ok)
	}

	val, ok = m.Get("bar")
	if !ok || val != 2 {
		t.Errorf("Expected bar=2, got %d (ok=%v)", val, ok)
	}

	// Verify version starts at 0
	if m.Version() != 0 {
		t.Errorf("Expected initial version to be 0, got %d", m.Version())
	}

	// Modify and check version increments
	m.Set("qux", 4)
	if m.Version() != 1 {
		t.Errorf("Expected version 1 after modification, got %d", m.Version())
	}
}

func TestFromMap(t *testing.T) {
	// Create a regular map
	regularMap := map[string]int{
		"foo": 1,
		"bar": 2,
		"baz": 3,
	}

	// Clone into sync Map
	m := FromMap(regularMap)

	// Verify contents
	if m.Len() != 3 {
		t.Errorf("Expected 3 entries from map, got %d", m.Len())
	}

	val, ok := m.Get("foo")
	if !ok || val != 1 {
		t.Errorf("Expected foo=1, got %d (ok=%v)", val, ok)
	}

	// Verify it's a clone - modifying original shouldn't affect sync Map
	regularMap["qux"] = 4
	if m.Has("qux") {
		t.Error("FromMap should clone, not reference original map")
	}

	// Modifying sync Map shouldn't affect original
	m.Set("extra", 99)
	if _, exists := regularMap["extra"]; exists {
		t.Error("Modifying sync Map should not affect original map")
	}

	// Test with empty map
	emptyMap := map[string]int{}
	m2 := FromMap(emptyMap)
	if m2.Len() != 0 {
		t.Errorf("Expected empty map, got %d entries", m2.Len())
	}

	// Test with nil map (should work but be empty)
	var nilMap map[string]int
	m3 := FromMap(nilMap)
	if m3.Len() != 0 {
		t.Errorf("Expected empty map from nil map, got %d entries", m3.Len())
	}
}

func TestClone(t *testing.T) {
	// Create and populate original map
	m := New[string, int]()
	m.Set("foo", 1)
	m.Set("bar", 2)
	m.Set("baz", 3)

	// Clone it
	clone := m.Clone()

	// Verify clone has same contents
	if clone.Len() != m.Len() {
		t.Errorf("Clone should have same length as original: expected %d, got %d", m.Len(), clone.Len())
	}

	for k, v := range m.All() {
		cloneVal, ok := clone.Get(k)
		if !ok {
			t.Errorf("Clone missing key %s", k)
		}
		if cloneVal != v {
			t.Errorf("Clone has wrong value for %s: expected %d, got %d", k, v, cloneVal)
		}
	}

	// Verify version is copied
	if clone.Version() != m.Version() {
		t.Errorf("Clone should have same version as original: expected %d, got %d", m.Version(), clone.Version())
	}

	// Verify it's a true clone - modifying original shouldn't affect clone
	m.Set("qux", 4)
	if clone.Has("qux") {
		t.Error("Clone should be independent - original modification affected clone")
	}

	// Modifying clone shouldn't affect original
	clone.Set("extra", 99)
	if m.Has("extra") {
		t.Error("Clone should be independent - clone modification affected original")
	}

	// Verify versions are independent (both should have incremented by 1 from the clone point)
	// After clone at v3: original did 1 set (v4), clone did 1 set (v4)
	// They happen to be the same value but are independently tracked
	originalVersion := m.Version()
	cloneVersion := clone.Version()
	if originalVersion != 4 || cloneVersion != 4 {
		t.Errorf("Expected both to be version 4, got original=%d, clone=%d", originalVersion, cloneVersion)
	}

	// Do different numbers of operations to show independence
	m.Set("alpha", 10)
	m.Set("beta", 20)     // original now at v6
	clone.Delete("extra") // clone now at v5

	if m.Version() == clone.Version() {
		t.Error("After different numbers of operations, versions should differ")
	}
	if m.Version() != 6 {
		t.Errorf("Original should be at version 6, got %d", m.Version())
	}
	if clone.Version() != 5 {
		t.Errorf("Clone should be at version 5, got %d", clone.Version())
	}

	// Test cloning empty map
	emptyMap := New[string, int]()
	emptyClone := emptyMap.Clone()
	if emptyClone.Len() != 0 {
		t.Errorf("Clone of empty map should be empty, got %d entries", emptyClone.Len())
	}
}

func TestCopy(t *testing.T) {
	// Create source map
	src := New[string, int]()
	src.Set("foo", 1)
	src.Set("bar", 2)
	src.Set("baz", 3)

	// Create destination map with some existing data
	dst := New[string, int]()
	dst.Set("qux", 4)
	dst.Set("bar", 99) // This should be overwritten

	initialVersion := dst.Version()

	// Copy from src to dst
	newVersion := dst.Copy(src)

	// Verify version incremented
	if newVersion != initialVersion+1 {
		t.Errorf("Expected version %d, got %d", initialVersion+1, newVersion)
	}

	// Verify dst has all entries from src
	if !dst.Has("foo") || !dst.Has("bar") || !dst.Has("baz") {
		t.Error("Destination should have all keys from source")
	}

	val, _ := dst.Get("foo")
	if val != 1 {
		t.Errorf("Expected foo=1, got %d", val)
	}

	// Verify overwrite happened
	val, _ = dst.Get("bar")
	if val != 2 {
		t.Errorf("Expected bar to be overwritten to 2, got %d", val)
	}

	// Verify dst still has its original entry
	val, ok := dst.Get("qux")
	if !ok || val != 4 {
		t.Errorf("Expected qux=4 to remain, got %d (ok=%v)", val, ok)
	}

	// Verify total length
	expectedLen := 4 // foo, bar, baz, qux
	if dst.Len() != expectedLen {
		t.Errorf("Expected destination to have %d entries, got %d", expectedLen, dst.Len())
	}

	// Test copying empty map
	emptySrc := New[string, int]()
	dst2 := New[string, int]()
	dst2.Set("existing", 1)
	dst2.Copy(emptySrc)
	if !dst2.Has("existing") {
		t.Error("Copying empty map should not remove existing entries")
	}

	// Test copying to empty map
	src2 := New[string, int]()
	src2.Set("alpha", 10)
	src2.Set("beta", 20)
	dst3 := New[string, int]()
	dst3.Copy(src2)
	if dst3.Len() != 2 {
		t.Errorf("Expected 2 entries after copying to empty map, got %d", dst3.Len())
	}
}

func TestCopyConcurrent(t *testing.T) {
	// Test that Copy is safe with concurrent modifications
	src := New[int, int]()
	dst := New[int, int]()

	// Populate source
	for i := range 100 {
		src.Set(i, i*2)
	}

	done := make(chan bool, 3)

	// Goroutine 1: Copy from src to dst repeatedly
	go func() {
		for range 10 {
			dst.Copy(src)
		}
		done <- true
	}()

	// Goroutine 2: Modify src concurrently
	go func() {
		for i := 100; i < 200; i++ {
			src.Set(i, i*2)
		}
		done <- true
	}()

	// Goroutine 3: Read from dst concurrently
	go func() {
		for range 100 {
			dst.Get(50)
			_ = dst.Len()
		}
		done <- true
	}()

	// Wait for completion
	for range 3 {
		<-done
	}

	// Verify dst is still functional
	dst.Set(999, 1998)
	val, ok := dst.Get(999)
	if !ok || val != 1998 {
		t.Errorf("Map should be functional after concurrent Copy operations")
	}
}

func TestTransferVsFromMap(t *testing.T) {
	// Create identical source maps
	map1 := map[string]int{"a": 1, "b": 2}
	map2 := map[string]int{"a": 1, "b": 2}

	// Transfer takes ownership
	transferred := Transfer(map1)
	// FromMap clones
	cloned := FromMap(map2)

	// Both should have same contents initially
	if transferred.Len() != cloned.Len() {
		t.Error("Transfer and FromMap should create maps with same initial length")
	}

	// Key difference: Transfer shares the underlying map (but you shouldn't use it)
	// FromMap is independent
	map2["c"] = 3 // This should NOT affect cloned
	if cloned.Has("c") {
		t.Error("FromMap should create independent map")
	}

	// We can't test Transfer's sharing behavior since using the original map
	// after Transfer is documented as incorrect usage
}

func TestCloneVersionTracking(t *testing.T) {
	m := New[string, int]()
	v0 := m.Version()

	m.Set("a", 1) // v1
	m.Set("b", 2) // v2

	clone := m.Clone()

	// Clone should have same version
	if clone.Version() != 2 {
		t.Errorf("Clone should have version 2, got %d", clone.Version())
	}

	// Original modifications
	m.Set("c", 3) // v3
	if m.Version() != 3 {
		t.Errorf("Original should have version 3, got %d", m.Version())
	}

	// Clone version should not change
	if clone.Version() != 2 {
		t.Errorf("Clone version should still be 2, got %d", clone.Version())
	}

	// Clone modifications
	clone.Set("d", 4)
	if clone.Version() != 3 {
		t.Errorf("Clone should now have version 3 (2+1), got %d", clone.Version())
	}

	// Original should still be at 3
	if m.Version() != 3 {
		t.Errorf("Original should still be version 3, got %d", m.Version())
	}

	// Verify v0 is 0
	if v0 != 0 {
		t.Errorf("Initial version should be 0, got %d", v0)
	}
}

func TestString(t *testing.T) {
	m := New[string, int]()
	m.Set("cherry", 8)
	m.Set("apple", 5)
	m.Set("banana", -3)
	// somehow the %v order is deterministic here
	expected := "map[apple:5 banana:-3 cherry:8]"
	actual := m.String()
	if actual != expected {
		t.Errorf("Expected String() to be %q, got %q", expected, actual)
	}
	actual2 := fmt.Sprintf("%v", m)
	if actual2 != expected {
		t.Errorf("Expected fmt %%v to be %q, got %q", expected, actual2)
	}
	actual3 := fmt.Sprintf("%s", m) //nolint:staticcheck // testing Stringer in fmt.
	if actual3 != expected {
		t.Errorf("Expected fmt %%s to be %q, got %q", expected, actual3)
	}
	// GoString
	expectedDebug := `*smap.Map[string,int](map[string]int{"apple":5, "banana":-3, "cherry":8})`
	actualDebug := m.GoString()
	if actualDebug != expectedDebug {
		t.Errorf("Expected GoString() to be %q, got %q", expectedDebug, actualDebug)
	}

	actualDebug2 := fmt.Sprintf("%#v", m)
	if actualDebug2 != expectedDebug {
		t.Errorf("Expected fmt %%#v to be %q, got %q", expectedDebug, actualDebug2)
	}
	// also %+#v
	actualDebug3 := fmt.Sprintf("%+#v", m)
	if actualDebug3 != expectedDebug {
		t.Errorf("Expected fmt %%+#v to be %q, got %q", expectedDebug, actualDebug3)
	}
}

// Example demonstrates basic usage of the concurrent safe Map
// including creating, setting, getting, and iterating with All().
// The whole point though would be do to these operations concurrently from multiple goroutines.
func Example() {
	// Create a new concurrent safe map
	m := New[string, int]()

	// Add some entries
	m.Set("apple", 5)
	m.Set("banana", 3)
	m.Set("cherry", 8)

	// Get a specific value
	count, exists := m.Get("banana")
	if exists {
		fmt.Printf("Bananas: %d\n", count)
	}

	// Check the total count
	fmt.Printf("Total items: %d\n", m.Len())

	// Check if a key exists
	fmt.Printf("Has apple: %t\n", m.Has("apple"))

	// Iterate over all entries using range
	// Note: We collect and sort for deterministic output in this example
	var toDelete []string
	// Using m.All you can't mutate the map during iteration (use AllSorted or collect changes first, or
	// use KeysSnapshot or KeysValuesSnapshot first then mutate)
	for fruit, count := range m.All() {
		if count < 8 {
			toDelete = append(toDelete, fruit)
		}
	}
	m.Delete(toDelete...) // Delete multiple, after iteration
	fmt.Printf("After removing items with count < 8, total items: %d\n", m.Len())
	fmt.Printf("Map is now just %v\n", m)

	// Output:
	// Bananas: 3
	// Total items: 3
	// Has apple: true
	// After removing items with count < 8, total items: 1
	// Map is now just map[cherry:8]
}

// ExampleMap_AllSorted demonstrates using AllSorted with a custom struct
// to iterate over entries in a specific order.
func ExampleMap_AllSorted() {
	// Define a custom struct with multiple fields
	type Task struct {
		Name     string
		Priority int
	}

	// Create a map with Task keys
	m := New[Task, string]()

	// Add some tasks
	m.Set(Task{Name: "Fix bug", Priority: 1}, "In Progress")
	m.Set(Task{Name: "Write docs", Priority: 3}, "Not Started")
	m.Set(Task{Name: "Review PR", Priority: 2}, "Completed")
	m.Set(Task{Name: "Deploy", Priority: 1}, "Pending")

	// Iterate in priority order (lowest priority number first)
	// If priorities are equal, sort by name
	fmt.Println("Tasks by priority:")
	for task, status := range m.AllSorted(func(a, b Task) bool {
		if a.Priority != b.Priority {
			return a.Priority < b.Priority
		}
		return a.Name < b.Name
	}) {
		// Here it's ok to mutate during iteration:
		if task.Priority == 1 {
			m.Set(task, "Changed") // Update high priority tasks
		}
		newStatus, _ := m.Get(task)
		fmt.Printf("  [P%d] %s: %s (current: %s)\n", task.Priority, task.Name, status, newStatus)
	}

	// Output:
	// Tasks by priority:
	//   [P1] Deploy: Pending (current: Changed)
	//   [P1] Fix bug: In Progress (current: Changed)
	//   [P2] Review PR: Completed (current: Completed)
	//   [P3] Write docs: Not Started (current: Not Started)
}

// ExampleNaturalSort demonstrates sorting with naturally ordered types.
func ExampleNaturalSort() {
	// Create a map with ordered keys (strings, ints, etc.)
	scores := New[string, int]()
	scores.Set("Charlie", 85)
	scores.Set("Alice", 92)
	scores.Set("Bob", 78)

	// Iterate in natural (alphabetical) order
	fmt.Println("Scores (alphabetically):")
	for name, score := range NaturalSort(scores) {
		fmt.Printf("  %s: %d\n", name, score)
	}

	// Output:
	// Scores (alphabetically):
	//   Alice: 92
	//   Bob: 78
	//   Charlie: 85
}
