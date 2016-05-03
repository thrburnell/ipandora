import React from 'react'

const FormulaInput = ({ 
  onEnterPress = () => {}, 
  onKeyDown = () => {},
  clearOnEnter = true
}) => {

  let input

  return (
    <div>
      <input 
        ref={node => {
          input = node
        }}
        onKeyDown={e => {
          if (e.key == 'Enter') {
            onEnterPress(input.value)
            if (clearOnEnter) input.value=''
          } else {
            onKeyDown(input.value)
          }
        }}/>
    </div>
  )
}

export default FormulaInput

