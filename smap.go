// Package smap is a zero dependencies library that provides a generic, concurrent safe map
// with go1.24 iterators including optionally ordered keys iteration.
//
// This was originally developed for [fortio.org/tsync]
// which uses and battle tests it including for race conditions (there aren't any!).
package smap

import (
	"cmp"
	"fmt"
	"iter"
	"maps"
	"sort"
	"sync"
)

// Map is a concurrent safe map.
type Map[K comparable, V any] struct {
	mu      sync.RWMutex
	version uint64
	m       map[K]V
}

// KV is a key-value pair used for [Map.SetBatch] and returned by [Map.KeysValuesSnapshot] (optional).
type KV[K comparable, V any] struct {
	Key   K
	Value V
}

// New creates a new concurrent safe [Map].
func New[K comparable, V any]() *Map[K, V] {
	return &Map[K, V]{
		m: make(map[K]V),
	}
}

// Version returns the current version of the map. If any changes were made, the version is incremented by 1 each time.
func (s *Map[K, V]) Version() (current uint64) {
	s.mu.RLock()
	current = s.version
	s.mu.RUnlock()
	return current
}

// Set sets the value for the given key and returns the new version of the map.
func (s *Map[K, V]) Set(key K, value V) (newVersion uint64) {
	s.mu.Lock()
	s.m[key] = value
	s.version++
	newVersion = s.version
	s.mu.Unlock()
	return newVersion
}

// SetBatch sets multiple key-value pairs in a single lock/unlock batch (and returns the new version of the map).
func (s *Map[K, V]) SetBatch(kvs []KV[K, V]) (newVersion uint64) {
	s.mu.Lock()
	for _, kv := range kvs {
		s.m[kv.Key] = kv.Value
	}
	s.version++
	newVersion = s.version
	s.mu.Unlock()
	return newVersion
}

// Get retrieves the value for the given key.
func (s *Map[K, V]) Get(key K) (V, bool) {
	s.mu.RLock()
	value, ok := s.m[key]
	s.mu.RUnlock()
	return value, ok
}

// Delete removes the given keys from the map and returns the new version of the map.
func (s *Map[K, V]) Delete(key ...K) (newVersion uint64) {
	s.mu.Lock()
	for _, k := range key {
		delete(s.m, k)
	}
	s.version++
	newVersion = s.version
	s.mu.Unlock()
	return newVersion
}

// Has checks if the given key exists in the map.
func (s *Map[K, V]) Has(key K) bool {
	s.mu.RLock()
	_, ok := s.m[key]
	s.mu.RUnlock()
	return ok
}

// Len returns the number of entries in the map.
func (s *Map[K, V]) Len() int {
	s.mu.RLock()
	l := len(s.m)
	s.mu.RUnlock()
	return l
}

// Clear removes all entries from the map.
func (s *Map[K, V]) Clear() (newVersion uint64) {
	s.mu.Lock()
	clear(s.m)
	s.version++
	newVersion = s.version
	s.mu.Unlock()
	return newVersion
}

// All returns an iterator over key-value pairs from the map.
// This allows ranging over the sync Map like a regular map using Go 1.24+ iterators.
// The iteration takes a read lock for the duration of going over the entries.
// If you wish to modify the map during iteration, you should postpone to after the loop
// or use [Map.AllSorted] or [NaturalSort] which are doing 2 phases and the 2nd phase is
// without holding a lock. If using this one and wanting to mutate the map,
// accumulate entries in a slice and call Delete(toDeleteSlice...) or [Map.SetBatch] for instance.
func (s *Map[K, V]) All() iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		s.mu.RLock()
		defer s.mu.RUnlock()
		for k, v := range s.m {
			if !yield(k, v) {
				return
			}
		}
	}
}

// Values returns an iterator over values from the map.
// This allows ranging over just the values using Go 1.24+ iterators.
// Like [Map.All] this iterator takes a read lock for the duration of going over the entries.
func (s *Map[K, V]) Values() iter.Seq[V] {
	return func(yield func(V) bool) {
		s.mu.RLock()
		defer s.mu.RUnlock()
		for _, v := range s.m {
			if !yield(v) {
				return
			}
		}
	}
}

// Keys returns an iterator over keys from the map.
// This allows ranging over just the keys using Go 1.24+ iterators.
// Like [Map.All] this iterator takes a read lock for the duration of going over the entries.
func (s *Map[K, V]) Keys() iter.Seq[K] {
	return func(yield func(K) bool) {
		s.mu.RLock()
		defer s.mu.RUnlock()
		for k := range s.m {
			if !yield(k) {
				return
			}
		}
	}
}

// KeysSnapshot returns a snapshot slice of the current keys in the map.
// The snapshot is taken under a read lock.
func (s *Map[K, V]) KeysSnapshot() []K {
	s.mu.RLock()
	keys := make([]K, 0, len(s.m))
	for k := range s.m {
		keys = append(keys, k)
	}
	s.mu.RUnlock()
	return keys
}

// KeysValuesSnapshot returns a snapshot slice of the current key-value pairs in the map.
// The snapshot is taken under a read lock.
func (s *Map[K, V]) KeysValuesSnapshot() []KV[K, V] {
	s.mu.RLock()
	kvs := make([]KV[K, V], 0, len(s.m))
	for k, v := range s.m {
		kvs = append(kvs, KV[K, V]{Key: k, Value: v})
	}
	s.mu.RUnlock()
	return kvs
}

// KeysSorted returns an iterator over keys sorted using the provided comparison function.
// Unlike [Map.Keys], the map snapshot occurs under a read lock, but then sorting happens without holding the lock.
func (s *Map[K, V]) KeysSorted(less func(a, b K) bool) iter.Seq[K] {
	return func(yield func(K) bool) {
		keys := s.KeysSnapshot()
		sort.Slice(keys, func(i, j int) bool {
			return less(keys[i], keys[j])
		})
		for _, k := range keys {
			if !yield(k) {
				return
			}
		}
	}
}

// AllSorted returns an iterator over key-value pairs where keys are visited in the order defined by less.
// Unlike [Map.All] only the keys snapshot occurs under a read lock, then sorting and value lookups happen without
// holding it. Because of that, by the time a key is revisited later, it may have been deleted;
// such entries are skipped.
func (s *Map[K, V]) AllSorted(less func(a, b K) bool) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		s.mu.RLock()
		keys := make([]K, 0, len(s.m))
		for k := range s.m {
			keys = append(keys, k)
		}
		s.mu.RUnlock()

		sort.Slice(keys, func(i, j int) bool {
			return less(keys[i], keys[j])
		})

		for _, k := range keys {
			s.mu.RLock()
			v, ok := s.m[k]
			s.mu.RUnlock()
			if !ok {
				continue
			}
			if !yield(k, v) {
				return
			}
		}
	}
}

// Transfer moves the input map into a new concurrent safe [Map]. You must not use the
// input map after calling Transfer or it would defeat the concurrent safety.
// In most case use [FromMap] instead to clone the input map and not take ownership of it.
// Passing a nil map results in a Map with a nil underlying map which will not work.
func Transfer[K comparable, V any](m map[K]V) *Map[K, V] {
	return &Map[K, V]{
		m: m,
	}
}

// FromMap creates a new [Map] from the provided standard map by cloning its contents.
// Passing a nil map results in a Map with a nil underlying map which will not work.
func FromMap[K comparable, V any](m map[K]V) *Map[K, V] {
	return &Map[K, V]{
		m: maps.Clone(m),
	}
}

// Clone creates a copy of the Map.
func (s *Map[K, V]) Clone() *Map[K, V] {
	s.mu.RLock()
	clone := FromMap(s.m)
	clone.version = s.version
	s.mu.RUnlock()
	return clone
}

// Copy copies all key/value pairs from src adding them to the current map.
// When a key in src is already present in this map, the value will be overwritten
// by the value associated with the key in src.
// Read lock is acquired on src and write lock on this map during the operation.
// The new version of the map is returned (previous + 1).
// Because of this calling Copy in both directions between 2 maps would lead to a deadlock.
func (s *Map[K, V]) Copy(src *Map[K, V]) (newVersion uint64) {
	s.mu.Lock()
	src.mu.RLock()
	maps.Copy(s.m, src.m)
	s.version++
	newVersion = s.version
	src.mu.RUnlock()
	s.mu.Unlock()
	return newVersion
}

// String() returns a string representation of the map for debugging purposes (%s/%v).
func (s *Map[K, V]) String() (debug string) {
	s.mu.RLock()
	debug = fmt.Sprintf("%v", s.m)
	s.mu.RUnlock()
	return debug
}

// GoString() returns a string representation of the map for debugging purposes (%#v).
func (s *Map[K, V]) GoString() (debug string) {
	s.mu.RLock()
	debug = fmt.Sprintf("%T(%#v)", s, s.m)
	s.mu.RUnlock()
	return debug
}

// Transaction executes the provided function fn within a write lock, with access to the internal map.
func (s *Map[K, V]) Transaction(fn func(m map[K]V)) (newVersion uint64) {
	s.mu.Lock()
	defer s.mu.Unlock() // in case fn panics. we also pre bump the version ahead of calling fn for same reason.
	s.version++
	newVersion = s.version
	fn(s.m)
	return newVersion
}

// NaturalSort returns an iterator that visits key-value pairs in the natural order of Q (using <).
// This requires Q (K from the Map[Q, V]) to be an ordered type.
func NaturalSort[Q cmp.Ordered, V any](s *Map[Q, V]) iter.Seq2[Q, V] {
	return s.AllSorted(func(a, b Q) bool {
		return a < b
	})
}
